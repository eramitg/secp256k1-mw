/**********************************************************************
 * Copyright (c) 2017 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_BULLETPROOF_INNER_PRODUCT_IMPL
#define SECP256K1_MODULE_BULLETPROOF_INNER_PRODUCT_IMPL

#include "group.h"

#include "modules/bulletproof/main_impl.h"
#include "modules/bulletproof/generators.h"
#include "modules/bulletproof/util.h"

#define POPCOUNT(x)	(__builtin_popcountl((unsigned long)(x)))  /* TODO make these portable */
#define CTZ(x)	(__builtin_ctzl((unsigned long)(x)))

typedef struct {
    const secp256k1_scalar *a;
    const secp256k1_scalar *b;
    secp256k1_scalar xsq[SECP256K1_BULLETPROOF_MAX_DEPTH];
    secp256k1_scalar xsqinv[SECP256K1_BULLETPROOF_MAX_DEPTH];
    secp256k1_scalar xcache[SECP256K1_BULLETPROOF_MAX_DEPTH];
    const secp256k1_ge *geng;
    const secp256k1_ge *genh;
    const secp256k1_ge *lpt;
    const secp256k1_ge *rpt;
    secp256k1_ecmult_multi_callback *rangeproof_cb;
    void *rangeproof_cb_data;
    size_t n_rangeproof_points;
    size_t depth;
} secp256k1_bulletproof_innerproduct_vfy_ecmult_context;

/* Bulletproof rangeproof verification comes down to a single multiexponentiation of the form
 *
 *   P + (c-a*b)*x*G - sum_{i=1}^n [a*s'_i*G_i + b*s_i*H_i] + sum_{i=1}^log2(n) [x_i^-2 L_i + x_i^2 R_i
 *
 * which will equal infinity if the rangeproof is correct. Here
 *   - `G_i` and `H_i` are standard NUMS generators. `G` is the standard secp256k1 generator.
 *   - `P` and `c` are inputs to the proof, which claims that there exist `a_i` and `b_i`, `i` ranging
 *     from 0 to `n-1`, such that `P = sum_i [a_i G_i + b_i H_i]` and that `<{a_i}, {b_i}> = c`.
 *   - `a`, `b`, `L_i` and `R_i`are auxillary components of the proof, where `i` ranges from 0 to `log2(n)-1`.
 *   - `x_i = H(x_{i-1} || L_i || R_i)`, where `x_{-1}` is passed through the `commit` variable and
 *     must be a commitment to `P` and `c`.
 *   - `x` is a hash of `commit` and is used to rerandomize `c`. See Protocol 2 vs Protocol 1 in the paper.
 *   - `s_i` and `s'_i` are computed as follows.
 *
 * For each `i` between 0 and `n-1` inclusive, let `b_{ij}` be -1 (1) if the `j`th bit of `i` is zero (one).
 * Here `j` ranges from 0 to `log2(n)-1`. Then for each such `i` we define
 *   - `s_i = prod_j x_j^{b_{ij}}`
 *   - `s'_i = 1/s_i`
 *
 * Alternately we can define `s_i` and `s'_i` recursively as follows:
 *   - `s_0 = s`_{n - 1} = 1 / prod_j x_j`
 *   - `s_i = s'_{n - 1 - i} = s_{i - 2^j} * x_j^2` where `j = i & (i - 1)` is `i` with its least significant 1 set to 0.
 *
 * Our ecmult_multi function takes `(c - a*b)*x` directly and multiplies this by `G`. For every other
 * (scalar, point) pair it calls the following callback function, which takes an index and outputs a
 * pair. The function therefore has three regimes:
 *
 * For the first `2n` invocations, it alternately returns `(s'_{n - i}, G_{n - i})` and `(s_i, H_i)`,
 * where `i` is `floor(idx / 2)`. The reason for the funny indexing is that we use the above recursive
 * definition of `s_i` and `s'_i` which produces each element with only a single scalar multiplication,
 * but in this mixed order. (We start with an array of `x_j^2` for each `x_j`.)
 *
 * As a side-effect, whenever `n - i = 2^j` for some `j`, `s_i = x_j^{-1} * prod_{j' != j} x_{j'}`,
 * so `x_j^{-2} = s_i*s_0`. Therefore we compute an array of inverse squares during this computation,
 * using only one multiplication per. We will need it in the following step.
 *
 * For the next `2*log2(n)` invocations it alternately returns `(x_i^-2, L_i)` and `(x_i^2, R_i)`
 * where `i` is `idx - 2*n`.
 *
 * For the remaining invocations it passes through to another callback, `rangeproof_cb_data` which
 * computes `P`. The reason for this is that in practice `P` is usually defined by another multiexp
 * rather than being a known point, and it is more efficient to compute one exponentiation.
 *
 */
static int secp256k1_bulletproof_innerproduct_vfy_ecmult_callback(secp256k1_scalar *sc, secp256k1_ge *pt, size_t idx, void *data) {
    secp256k1_bulletproof_innerproduct_vfy_ecmult_context *ctx = (secp256k1_bulletproof_innerproduct_vfy_ecmult_context *) data;
    const size_t n = 1u << ctx->depth;

    /* First `n` points use the `G` generators, second `n` use the `H` generators... */
    if (idx < 2 * n) {
        const size_t cache_idx = POPCOUNT(idx / 2);
        secp256k1_scalar ab;
        const secp256k1_ge *gh;
        size_t mask;
        int doing_g;
        if (idx % 2 == 0) {
            secp256k1_scalar_negate(&ab, ctx->a);
            gh = ctx->geng;
            mask = n - 1;
            doing_g = 1;
        } else {
            secp256k1_scalar_negate(&ab, ctx->b);
            gh = ctx->genh;
            mask = 0;
            doing_g = 0;
        }
        idx /= 2;

        /* For the G and H generators, we choose the ith generator with a scalar computed from the
         * L/R hashes as follows: prod_{j=1}^m x_j^{e_j}, where each exponent e_j is either -1 or 1.
         * The choice directly maps to the bits of i: for the G generators, a 0 bit means e_j is 1
         * and a 1 bit means e_j is -1. For the H generators it is the opposite. Finally, each of the
         * G scalars is further multiplied by -a, while each of the H scalars is further multiplied
         * by -b.
         *
         * These scalars are computed starting from I, the inverse of the product of every x_j, which
         * is then selectively multiplied by x_j^2 for whichever j's are needed. As it turns out, by
         * caching logarithmically many scalars, this can always be done by multiplying one of the
         * cached values by a single x_j, rather than starting from I and doing multiple multiplications.
         */
        VERIFY_CHECK(cache_idx < SECP256K1_BULLETPROOF_MAX_DEPTH);
        /* we alternate G and H generators .. for G compute and cache the scalar,
         * for H just use the cache. For scalars of the form x_j^-1 prod_{j' != j} x_{j'},
         * also multiply by the product of all inverses (which is always in xcache[0]) to
         * compute x_j^-2, which we'll need later.
         */
        if (doing_g) {
            const size_t notidx = idx ^ mask;
            if (cache_idx > 0) {
                secp256k1_scalar_mul(&ctx->xcache[cache_idx], &ctx->xcache[cache_idx - 1], &ctx->xsq[ctx->depth - 1 - CTZ(idx)]);
            }
            if (POPCOUNT(notidx) == 1) {  /* our scalar has exactly one inverse, x_j with j = CTZ(~idx) */
                /* multiply the scalar with the total inverse, leaving us with x_j^-2 */
                secp256k1_scalar_mul(&ctx->xsqinv[ctx->depth - 1 - CTZ(notidx)], &ctx->xcache[cache_idx], &ctx->xcache[0]);
            }
        }
        secp256k1_scalar_mul(sc, &ctx->xcache[cache_idx], &ab);

        if (ctx->rangeproof_cb != NULL) {
            secp256k1_scalar rangeproof_offset;
            if ((ctx->rangeproof_cb)(&rangeproof_offset, NULL, idx ^ mask, ctx->rangeproof_cb_data) == 0) {
                return 0;
            }
            if (doing_g == 0) {
                secp256k1_scalar_mul(sc, sc, (secp256k1_scalar *) ctx->rangeproof_cb_data);
            }
            secp256k1_scalar_add(sc, sc, &rangeproof_offset);
        }
        *pt = gh[idx ^ mask];
    }
    /* ...next `2*log2(n)` points use the `lpt` and `rpt` arrays alternately... */
    else if (idx < 2 * n + 2 * ctx->depth) {
        const secp256k1_scalar *xxinv;
        const secp256k1_ge *lr;

        idx -= 2 * n;
        if (idx % 2 == 0) {
            xxinv = ctx->xsqinv;
            lr = ctx->lpt;
        } else {
            xxinv = ctx->xsq;
            lr = ctx->rpt;
        }
        idx /= 2;
        *pt = lr[idx];
        *sc = xxinv[idx];
    } else {
        VERIFY_CHECK(idx < 2 * n + 2 * ctx->depth + ctx->n_rangeproof_points);
        if ((ctx->rangeproof_cb)(sc, pt, idx, ctx->rangeproof_cb_data) == 0) {
            return 0;
        }
    }
    return 1;
}

/* nb For security it is essential that `commit_inp` already commit to all data
 *    needed to compute `P`. We do not hash it in during verification since `P`
 *    may be specified indirectly as a bunch of scalar offsets.
 */
static int secp256k1_bulletproof_inner_product_verify_impl(const secp256k1_ecmult_context *ecmult_ctx, secp256k1_scratch *scratch, const secp256k1_ge *geng, const secp256k1_ge *genh, const secp256k1_scalar *dot, const secp256k1_ge *p, const secp256k1_scalar *p_offs, secp256k1_ecmult_multi_callback rangeproof_ecmult_cb, void *rangeproof_ecmult_cb_data, size_t n_extra_rangeproof_pts, const secp256k1_scalar *a, const secp256k1_scalar *b, const secp256k1_ge *lpt, const secp256k1_ge *rpt, const size_t depth, const unsigned char *commit_inp) {
    secp256k1_bulletproof_innerproduct_vfy_ecmult_context ecmult_data;
    const size_t n_points = (2 << depth) + 2 * depth + n_extra_rangeproof_pts;
    secp256k1_scalar negprod;
    secp256k1_gej r;
    size_t i;
    unsigned char commit[32];
    int overflow;
    secp256k1_scalar x;
    secp256k1_scalar zero;

    secp256k1_scalar_clear(&zero);
    memcpy(commit, commit_inp, 32);
    /* Set all data except total inverse and the hash arrays directly from the input */
    ecmult_data.depth = depth;
    ecmult_data.rangeproof_cb = rangeproof_ecmult_cb;
    ecmult_data.rangeproof_cb_data = rangeproof_ecmult_cb_data;
    ecmult_data.n_rangeproof_points = n_extra_rangeproof_pts;
    ecmult_data.geng = geng;
    ecmult_data.genh = genh;
    ecmult_data.lpt = lpt;
    ecmult_data.rpt = rpt;
    ecmult_data.a = a;
    ecmult_data.b = b;

    /* Randomize claimed inner-product */
    secp256k1_scalar_set_b32(&x, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&x)) {
        return 0;
    }
    secp256k1_scalar_mul(&negprod, a, b);
    secp256k1_scalar_negate(&negprod, &negprod);
    secp256k1_scalar_add(&negprod, &negprod, dot);
    secp256k1_scalar_mul(&x, &x, &negprod);
    secp256k1_scalar_add(&x, &x, p_offs);

    /* Compute the inverse product and the array of squares; the rest will be filled
     * in by the callback during the multiexp. */
    secp256k1_scalar_set_int(&ecmult_data.xcache[0], 1);
    for (i = 0; i < depth; i++) {
        secp256k1_scalar xi;
        /* Map commit -> H(commit || LR parity || Lx || Rx), compute xi from it */
        secp256k1_bulletproof_update_commit(commit, &lpt[i], &rpt[i]);
        secp256k1_scalar_set_b32(&xi, commit, &overflow);
        if (overflow || secp256k1_scalar_is_zero(&xi)) {
            return 0;
        }
        secp256k1_scalar_mul(&ecmult_data.xcache[0], &ecmult_data.xcache[0], &xi);
        secp256k1_scalar_sqr(&ecmult_data.xsq[i], &xi);
    }
    secp256k1_scalar_inverse_var(&ecmult_data.xcache[0], &ecmult_data.xcache[0]);

    /* Do the multiexp */
    if (secp256k1_ecmult_multi_var(ecmult_ctx, scratch, &r, &x, secp256k1_bulletproof_innerproduct_vfy_ecmult_callback, (void *) &ecmult_data, n_points) != 1) {
        return 0;
    }
    secp256k1_gej_add_ge_var(&r, &r, p, NULL);
    return secp256k1_gej_is_infinity(&r);
}

static void secp256k1_scalar_dot_product(secp256k1_scalar *r, const secp256k1_scalar *a, const secp256k1_scalar *b, size_t n) {
    secp256k1_scalar_clear(r);
    while(n--) {
        secp256k1_scalar term;
        secp256k1_scalar_mul(&term, &a[n], &b[n]);
        secp256k1_scalar_add(r, r, &term);
    }
}

/* These proofs are not zero-knowledge. There is no need to worry about constant timeness.
 * Having said that, we avoid using ecmult_multi because it'd clobber our scratch space.
 * `commit_inp` must contain 256 bits of randomness, it is used immediately as a randomizer.
 */
static int secp256k1_bulletproof_inner_product_prove_impl(const secp256k1_ecmult_context *ecmult_ctx, secp256k1_scratch *scratch, secp256k1_scalar *final_a, secp256k1_scalar *final_b, secp256k1_ge *lpt_arr, secp256k1_ge *rpt_arr, const size_t depth, secp256k1_ecmult_multi_callback *cb, void *cb_data, const unsigned char *commit_inp) {
    size_t n;
    secp256k1_scalar zero;
    size_t i;
    unsigned char commit[32];
    secp256k1_scalar *a_arr;
    secp256k1_scalar *b_arr;
    secp256k1_gej *geng;
    secp256k1_gej *genh;
    secp256k1_scalar ux;
    int overflow;

    /* setup */
    VERIFY_CHECK(depth < SECP256K1_BULLETPROOF_MAX_DEPTH);
    n = 1u << depth;

    secp256k1_scalar_clear(&zero);

    if (!secp256k1_scratch_resize(scratch, 2 * n * (sizeof(secp256k1_scalar) + sizeof(secp256k1_gej)), 4)) {
        return 0;
    }
    secp256k1_scratch_reset(scratch);
    a_arr = (secp256k1_scalar*)secp256k1_scratch_alloc(scratch, n * sizeof(secp256k1_scalar));
    b_arr = (secp256k1_scalar*)secp256k1_scratch_alloc(scratch, n * sizeof(secp256k1_scalar));
    geng = (secp256k1_gej*)secp256k1_scratch_alloc(scratch, n * sizeof(secp256k1_gej));
    genh = (secp256k1_gej*)secp256k1_scratch_alloc(scratch, n * sizeof(secp256k1_gej));

    memcpy(commit, commit_inp, 32);
    for (i = 0; i < n; i++) {
        secp256k1_ge tmpge;
        cb(&a_arr[i], &tmpge, 2*i, cb_data);
        secp256k1_gej_set_ge(&geng[i], &tmpge);
        cb(&b_arr[i], &tmpge, 2*i+1, cb_data);
        secp256k1_gej_set_ge(&genh[i], &tmpge);
    }

    /* Protocol 2: obtain randomizer */
    secp256k1_scalar_set_b32(&ux, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&ux)) {
        return 0;
    }

    /* Protocol 1: Iterate, halving vector size until it is 1 */
    for (i = 0; i < depth; i++) {
        const size_t halfwidth = n >> (i + 1);
        secp256k1_gej tmplj, tmprj;
        secp256k1_scalar x, xinv;
        size_t j;

        /* L */
        secp256k1_gej_set_infinity(&tmplj);
        for (j = 0; j < halfwidth; j++) {
            secp256k1_gej tmpj;
            if (j == 0) {
                secp256k1_scalar tmps;
                secp256k1_scalar_dot_product(&tmps, &a_arr[0], &b_arr[halfwidth], halfwidth);
                secp256k1_scalar_mul(&tmps, &tmps, &ux);
                secp256k1_ecmult(ecmult_ctx, &tmpj, &geng[halfwidth + j], &a_arr[j], &tmps);
            } else {
                secp256k1_ecmult(ecmult_ctx, &tmpj, &geng[halfwidth + j], &a_arr[j], &zero);
            }
            secp256k1_gej_add_var(&tmplj, &tmplj, &tmpj, NULL);
            secp256k1_ecmult(ecmult_ctx, &tmpj, &genh[j], &b_arr[halfwidth + j], &zero);
            secp256k1_gej_add_var(&tmplj, &tmplj, &tmpj, NULL);
        }
        secp256k1_ge_set_gej(&lpt_arr[i], &tmplj);
        /* R */
        secp256k1_gej_set_infinity(&tmprj);
        for (j = 0; j < halfwidth; j++) {
            secp256k1_gej tmpj;
            if (j == 0) {
                secp256k1_scalar tmps;
                secp256k1_scalar_dot_product(&tmps, &b_arr[0], &a_arr[halfwidth], halfwidth);
                secp256k1_scalar_mul(&tmps, &tmps, &ux);
                secp256k1_ecmult(ecmult_ctx, &tmpj, &geng[j], &a_arr[halfwidth + j], &tmps);
            } else {
                secp256k1_ecmult(ecmult_ctx, &tmpj, &geng[j], &a_arr[halfwidth + j], &zero);
            }
            secp256k1_gej_add_var(&tmprj, &tmprj, &tmpj, NULL);
            secp256k1_ecmult(ecmult_ctx, &tmpj, &genh[halfwidth + j], &b_arr[j], &zero);
            secp256k1_gej_add_var(&tmprj, &tmprj, &tmpj, NULL);
        }
        secp256k1_ge_set_gej(&rpt_arr[i], &tmprj);

        /* x, x^2, x^-1, x^-2 */
        secp256k1_bulletproof_update_commit(commit, &lpt_arr[i], &rpt_arr[i]);
        secp256k1_scalar_set_b32(&x, commit, &overflow);
        if (overflow || secp256k1_scalar_is_zero(&x)) {
            return 0;
        }
        secp256k1_scalar_inverse_var(&xinv, &x);

        /* update generators and scalar array */
        for (j = 0; j < halfwidth; j++) {
            secp256k1_scalar tmps;
            secp256k1_gej tmp1j, tmp2j;

            secp256k1_ecmult(ecmult_ctx, &tmp1j, &geng[j], &x, &zero);
            secp256k1_ecmult(ecmult_ctx, &tmp2j, &geng[j + halfwidth], &xinv, &zero);
            secp256k1_gej_add_var(&geng[j], &tmp1j, &tmp2j, NULL);

            secp256k1_ecmult(ecmult_ctx, &tmp1j, &genh[j], &xinv, &zero);
            secp256k1_ecmult(ecmult_ctx, &tmp2j, &genh[j + halfwidth], &x, &zero);
            secp256k1_gej_add_var(&genh[j], &tmp1j, &tmp2j, NULL);

            secp256k1_scalar_mul(&a_arr[j], &a_arr[j], &xinv);
            secp256k1_scalar_mul(&tmps, &a_arr[j + halfwidth], &x);
            secp256k1_scalar_add(&a_arr[j], &a_arr[j], &tmps);

            secp256k1_scalar_mul(&b_arr[j], &b_arr[j], &x);
            secp256k1_scalar_mul(&tmps, &b_arr[j + halfwidth], &xinv);
            secp256k1_scalar_add(&b_arr[j], &b_arr[j], &tmps);
        }
    }

    *final_a = a_arr[0];
    *final_b = b_arr[0];
    return 1;
}

#endif
