#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#ifdef _WIN32
#include <windows.h>
#include <bcrypt.h>
#endif

typedef struct { uint8_t s[2][16]; } State; /* row-major nibbles */
typedef struct { uint8_t s[2]; } Bit;
static const uint8_t sbox[16] = {12,5,6,11,9,0,10,13,3,14,15,8,4,7,1,2};
static const uint16_t anf[4] = {0x0152,0x3d84,0x2f19,0x29c7};
static const uint8_t mds[4][4] = {
    {4,1,2,2}, {8,6,5,6}, {11,14,10,9}, {2,2,15,11}
};
static const uint8_t ac[2][16] = {
    {0,0,0,0, 1,1,0,0, 2,0,0,0, 3,1,0,0},
    {0,0,0,0, 2,1,0,0, 2,0,0,0, 3,1,0,0}
};
static uint8_t rng_pool[4096];
static size_t rng_pos = sizeof rng_pool;
static uint64_t bit_requests;
#ifndef _WIN32
static FILE *rng_file;
#endif

static void refill_rng(void) {
#ifdef _WIN32
    if (BCryptGenRandom(NULL, rng_pool, (ULONG)sizeof rng_pool,
                       BCRYPT_USE_SYSTEM_PREFERRED_RNG) != 0) {
        fputs("OS RNG failed\n", stderr); exit(EXIT_FAILURE);
    }
#else
    if (!rng_file) rng_file = fopen("/dev/urandom", "rb");
    if (!rng_file || fread(rng_pool, 1, sizeof rng_pool, rng_file) != sizeof rng_pool) {
        fputs("OS RNG failed\n", stderr); exit(EXIT_FAILURE);
    }
#endif
    rng_pos = 0;
}
static uint8_t random_byte(void) {
    if (rng_pos == sizeof rng_pool) refill_rng();
    return rng_pool[rng_pos++];
}
static uint8_t random_bit(void) {
    ++bit_requests;
    return random_byte() & 1u; /* simple model: one byte consumed per bit */
}
static Bit bxor(Bit a, Bit b) {
    Bit c = {{(uint8_t)(a.s[0]^b.s[0]), (uint8_t)(a.s[1]^b.s[1])}};
    return c;
}
static Bit refresh(Bit a) {
    uint8_t r = random_bit();
    a.s[0] ^= r; a.s[1] ^= r;
    return a;
}
static Bit masked_and(Bit a, Bit b) {
    /* Refresh both operands independently, including correlated operands.
     * Every call receives three fresh bits: two refresh bits + one ISW bit.
     * Correctness: c0 XOR c1 = (a0 XOR a1) AND (b0 XOR b1).
     * This C source expresses an ideal Boolean circuit, not physical security.
     */
    a = refresh(a); b = refresh(b);
    uint8_t r = random_bit();
    uint8_t t = r ^ (a.s[0] & b.s[1]);
    t ^= a.s[1] & b.s[0];
    Bit c = {{(uint8_t)((a.s[0]&b.s[0])^r),
              (uint8_t)((a.s[1]&b.s[1])^t)}};
    return c;
}
static void masked_sbox(uint8_t *a0, uint8_t *a1) {
    /* Evaluate PRESENT S-box ANF on shared BITS. No secret table index,
     * no input reconstruction. Bit 0 is the least significant nibble bit.
     * mon[m] is the product of input bits selected by public mask m.
     */
    Bit mon[16];
    mon[0] = (Bit){{1,0}};
    for (unsigned k=0; k<4; ++k)
        mon[1u<<k] = (Bit){{(uint8_t)((*a0>>k)&1u),
                            (uint8_t)((*a1>>k)&1u)}};
    for (unsigned m=1; m<16; ++m) {
        unsigned low = m & (0u-m);
        if (m != low) mon[m] = masked_and(mon[m^low], mon[low]);
    }
    uint8_t y0=0, y1=0;
    for (unsigned k=0; k<4; ++k) {
        Bit y = {{0,0}};
        for (unsigned m=0; m<16; ++m)
            if ((anf[k]>>m)&1u) y = bxor(y, mon[m]);
        y = refresh(y);
        y0 |= (uint8_t)(y.s[0]<<k); y1 |= (uint8_t)(y.s[1]<<k);
    }
    *a0=y0; *a1=y1;
}
static uint8_t gf_mul(uint8_t a, uint8_t b) {
    /* GF(16), modulus x^4+x+1. b is always a PUBLIC MDS coefficient. */
    uint8_t z=0;
    for (unsigned k=0; k<4; ++k) {
        z ^= a & (uint8_t)(0u-(b&1u));
        uint8_t carry = (a>>3)&1u;
        a = (uint8_t)(((a<<1)&15u) ^ (3u & (0u-carry)));
        b >>= 1;
    }
    return z;
}
static void shift_rows(uint8_t a[16]) {
    uint8_t t[16];
    for (unsigned r=0; r<4; ++r)
        for (unsigned c=0; c<4; ++c) t[4*r+c] = a[4*r+(c+r)%4];
    memcpy(a,t,16);
}
static void mix_columns(uint8_t a[16]) {
    uint8_t t[16]={0};
    for (unsigned c=0; c<4; ++c)
        for (unsigned r=0; r<4; ++r)
            for (unsigned k=0; k<4; ++k)
                t[4*r+c] ^= gf_mul(a[4*k+c], mds[r][k]);
    memcpy(a,t,16);
}
static uint64_t pack(const uint8_t a[16]) {
    uint64_t v=0;
    for (unsigned j=0; j<16; ++j) v=(v<<4)|a[j];
    return v;
}
static void unpack(uint64_t v, uint8_t a[16]) {
    for (unsigned j=0; j<16; ++j) a[j]=(uint8_t)((v>>(60-4*j))&15u);
}
static State share_input(uint64_t v) {
    State a; uint8_t plain[16]; unpack(v,plain);
    for (unsigned j=0; j<16; ++j) {
        a.s[0][j]=random_byte()&15u;
        a.s[1][j]=plain[j]^a.s[0][j];
    }
    return a;
}
static uint64_t reconstruct(const State *a) {
    /* Only used by display/tests, never by the masked permutation. */
    return pack(a->s[0])^pack(a->s[1]);
}
static void show(const char *label, const State *a) {
    printf("%s\n  share 0: %016" PRIx64 "\n  share 1: %016" PRIx64
           "\n  XOR    : %016" PRIx64 "\n", label,
           pack(a->s[0]),pack(a->s[1]),reconstruct(a));
}
static void trace_stage(const char *label, const State *a) {
    show(label,a);
    uint8_t t[16]; unpack(reconstruct(a),t);
    for (unsigned r=0; r<4; ++r) {
        printf("  ");
        for (unsigned c=0; c<4; ++c) printf("%x ",t[4*r+c]);
        puts("");
    }
}
static State masked_f(State a, unsigned f, int trace) {
    for (unsigned round=0; round<2; ++round) {
        if (trace) printf("\nF%u LED round %u\n",f+1,round+1);
        if (round==0)
            for (unsigned j=0; j<16; ++j) a.s[0][j]^=ac[f][j];
        if (trace) trace_stage("after AddConstants (AC)",&a);
        for (unsigned j=0; j<16; ++j) masked_sbox(&a.s[0][j],&a.s[1][j]);
        if (trace) trace_stage("after SubCells (SC)",&a);
        for (unsigned d=0; d<2; ++d) shift_rows(a.s[d]);
        if (trace) trace_stage("after ShiftRows (SR)",&a);
        for (unsigned d=0; d<2; ++d) mix_columns(a.s[d]);
        if (trace) trace_stage("after MixColumnsSerial (MCS)",&a);
    }
    return a;
}
static uint64_t reference_f(uint64_t v, unsigned f) {
    /* UNMASKED oracle used only for testing public test inputs. */
    uint8_t a[16]; unpack(v,a);
    for (unsigned round=0; round<2; ++round) {
        if (round==0) for (unsigned j=0; j<16; ++j) a[j]^=ac[f][j];
        for (unsigned j=0; j<16; ++j) a[j]=sbox[a[j]];
        shift_rows(a); mix_columns(a);
    }
    return pack(a);
}
static State state_xor(State a, State b) {
    for (unsigned d=0; d<2; ++d)
        for (unsigned j=0; j<16; ++j) a.s[d][j]^=b.s[d][j];
    return a;
}
static void permutation_round(const State x[4], State y[4], State *u,
                              State *v, int trace) {
    *u=masked_f(x[0],0,trace); *v=masked_f(x[2],1,trace);
    State t[4];
    t[0]=state_xor(x[1],*u); t[1]=x[2];
    t[2]=state_xor(x[3],*v); t[3]=x[0];
    memcpy(y,t,sizeof t);
}
static int self_test(void) {
    /* All possible S-box input sharings, repeated with fresh gadget masks. */
    for (unsigned repeat=0; repeat<8; ++repeat)
        for (unsigned x=0; x<16; ++x)
            for (unsigned mask=0; mask<16; ++mask) {
                uint8_t a=(uint8_t)mask,b=(uint8_t)(x^mask);
                masked_sbox(&a,&b);
                if ((a^b)!=sbox[x]) return 0;
            }
    if (reference_f(UINT64_C(0x0001020304050607),0)!=UINT64_C(0xbe0dd493dc9b18dd)
        || reference_f(UINT64_C(0x0001020304050607),1)!=UINT64_C(0xefe72fb419228628))
        return 0;
    for (unsigned test=0; test<200; ++test) {
        State x[4],y[4],u,v; uint64_t plain[4];
        for (unsigned j=0; j<4; ++j) {
            plain[j]=0;
            for (unsigned k=0; k<8; ++k) plain[j]=(plain[j]<<8)|random_byte();
            x[j]=share_input(plain[j]);
        }
        permutation_round(x,y,&u,&v,0);
        if (reconstruct(&u)!=reference_f(plain[0],0)
            || reconstruct(&v)!=reference_f(plain[2],1)
            || reconstruct(&y[0])!=(plain[1]^reference_f(plain[0],0))
            || reconstruct(&y[1])!=plain[2]
            || reconstruct(&y[2])!=(plain[3]^reference_f(plain[2],1))
            || reconstruct(&y[3])!=plain[0]) return 0;
    }
    puts("PASS: all 256 S-box sharings x 8 repetitions; supplied F1/F2 vectors; 200 random four-branch rounds.");
    puts("These are functional tests, not a leakage/security proof.");
    return 1;
}
int main(int argc, char **argv) {
    int trace=1, testing=0;
    if (argc==2 && strcmp(argv[1],"--trace")==0) trace=1;
    else if (argc==2 && strcmp(argv[1],"--quiet")==0) trace=0;
    else if (argc==2 && strcmp(argv[1],"--self-test")==0) testing=1;
    else if (argc!=1) {
        fprintf(stderr,"Usage: %s [--trace | --quiet | --self-test]\n",argv[0]); return EXIT_FAILURE;
    }
    int result=EXIT_SUCCESS;
    if (testing) result=self_test()?EXIT_SUCCESS:EXIT_FAILURE;
    else {
        const uint64_t input[4]={UINT64_C(0x0001020304050607),
            UINT64_C(0x08090a0b0c0d0e0f),UINT64_C(0x0001020304050607),
            UINT64_C(0x08090a0b0c0d0e0f)};
        State x[4],y[4],u,v;
        puts("Educational masking demo: printed shares/intermediates are NOT secret.");
        puts("One outer permutation round; two LED rounds per F; constants exactly as supplied.");
        for (unsigned j=0; j<4; ++j) {
            char label[16]; snprintf(label,sizeof label,"X%u",j+1);
            x[j]=share_input(input[j]); show(label,&x[j]);
        }
        bit_requests=0;
        permutation_round(x,y,&u,&v,trace);
        show("F1 output (U0,U1)",&u); show("F2 output (V0,V1)",&v);
        for (unsigned j=0; j<4; ++j) {
            char label[16]; snprintf(label,sizeof label,"Y%u",j+1); show(label,&y[j]);
        }
        printf("Fresh random bits requested inside F1+F2: %" PRIu64 "\n",bit_requests);
        puts("Initial sharing additionally used 256 mask bits; byte-oriented RNG deliberately wastes unused bits.");
        if (reconstruct(&u)!=UINT64_C(0xbe0dd493dc9b18dd)
            || reconstruct(&v)!=UINT64_C(0xefe72fb419228628)) {
            fputs("FAIL: supplied output mismatch\n",stderr); result=EXIT_FAILURE;
        } else puts("PASS: both supplied F outputs match.");
    }
#ifndef _WIN32
    if (rng_file) fclose(rng_file);
#endif
    return result;
}