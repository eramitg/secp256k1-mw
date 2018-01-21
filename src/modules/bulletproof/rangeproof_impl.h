/**********************************************************************
 * Copyright (c) 2017 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_BULLETPROOF_RANGEPROOF_IMPL
#define SECP256K1_MODULE_BULLETPROOF_RANGEPROOF_IMPL

#include "modules/bulletproof/inner_product_impl.h"
#include "modules/bulletproof/util.h"
#include "group.h"

#define MAX_NBITS	64

typedef struct {
    secp256k1_scalar mul_by;
    secp256k1_scalar yinv;
    secp256k1_scalar z;
    secp256k1_scalar zsq;
    secp256k1_scalar negz;
    secp256k1_scalar x;
    secp256k1_ge s;
    size_t parity;
    size_t n;
    /* eq (61) stuff */
    size_t count;
    secp256k1_scalar randomizer61;
    secp256k1_scalar y;
    secp256k1_scalar t;
    const secp256k1_ge *asset;
    const secp256k1_ge *commit;
    secp256k1_ge t1;
    secp256k1_ge t2;
} secp256k1_bulletproof_vfy_ecmult_context;

static int secp256k1_bulletproof_vfy_ecmult_callback(secp256k1_scalar *sc, secp256k1_ge *pt, size_t idx, void *data) {
    secp256k1_bulletproof_vfy_ecmult_context *ctx = (secp256k1_bulletproof_vfy_ecmult_context *) data;

    if (idx < ctx->n) {
        if (ctx->parity == 0) {
            *sc = ctx->negz;
        } else {
            secp256k1_scalar_add(sc, &ctx->zsq, &ctx->z);
            secp256k1_scalar_mul(&ctx->zsq, &ctx->zsq, &ctx->yinv);
            secp256k1_scalar_add(&ctx->zsq, &ctx->zsq, &ctx->zsq);
            secp256k1_scalar_mul(&ctx->mul_by, &ctx->mul_by, &ctx->yinv);
        }
        ctx->parity = !ctx->parity;
    } else {
        switch(ctx->count) {
        /* S^x in eq (62) */
        case 0:
            *sc = ctx->x;
            *pt = ctx->s;
            break;
        case 1: {
            size_t i;
            secp256k1_scalar yn;
            secp256k1_scalar twon;
            secp256k1_scalar tmp;

            secp256k1_scalar_set_int(&twon, 1);
            secp256k1_scalar_set_int(&yn, 1);
            secp256k1_scalar_set_int(&tmp, 1);

            secp256k1_scalar_sqr(&ctx->zsq, &ctx->z);  /* need to re-set this */
            secp256k1_scalar_negate(sc, &ctx->zsq);  /* -z^2 */
            secp256k1_scalar_add(sc, sc, &ctx->z);   /* z - z^2 */

            for (i = 0; i < ctx->n - 1; i++) {
                secp256k1_scalar_mul(&yn, &yn, &ctx->y);
                secp256k1_scalar_add(&twon, &twon, &twon);

                secp256k1_scalar_add(&yn, &yn, &tmp);
                secp256k1_scalar_add(&twon, &twon, &tmp);
            }  /* yn = 1 + y + ... + y^(n-1); twon = 1 + 2 + ... + 2^(n-1) */
            secp256k1_scalar_mul(&tmp, &ctx->zsq, &ctx->negz);
            secp256k1_scalar_mul(&twon, &twon, &tmp);

            secp256k1_scalar_mul(sc, sc, &yn);    /* (z - z^2)(1 + ... + y^(n-1)) */
            secp256k1_scalar_add(sc, sc, &twon);  /* (z - z^2)(1 + ... + y^(n-1)) - z^3(1 + ... + 2^(n-1)) */
            secp256k1_scalar_negate(&tmp, &ctx->t);
            secp256k1_scalar_add(sc, sc, &tmp);    /* (z - z^2)(1 + ... + y^n) - z^3(1 + ... + 2^n) - t */
            secp256k1_scalar_mul(sc, sc, &ctx->randomizer61);
            *pt = *ctx->asset;
            break;
        }
        /* V^z^2 in eq (61) */
        case 2:
            secp256k1_scalar_mul(sc, &ctx->zsq, &ctx->randomizer61);
            *pt = *ctx->commit;
            break;
        /* A^[k(y, z) + sum_i y^i - t] from eq (61) */
        /* T1^x in eq (61) */
        case 3:
            secp256k1_scalar_mul(sc, &ctx->x, &ctx->randomizer61);
            *pt = ctx->t1;
            break;
        /* T2^x^2 in eq (61) */
        case 4:
            secp256k1_scalar_sqr(sc, &ctx->x);
            secp256k1_scalar_mul(sc, sc, &ctx->randomizer61);
            *pt = ctx->t2;
            break;
        default:
            VERIFY_CHECK(!"bulletproof: too many points added by rangeproof_verify_impl to inner_product_verify_impl");
        }
        ctx->count++;
    }
    return 1;
}

static int secp256k1_bulletproof_rangeproof_verify_impl(const secp256k1_ecmult_context *ecmult_ctx, secp256k1_scratch *scratch, const unsigned char *proof, size_t plen, size_t nbits, const secp256k1_ge *commitp, const secp256k1_ge *genp, const secp256k1_ge *geng, const secp256k1_ge *genh, const unsigned char *extra_commit, size_t extra_commit_len) {
    secp256k1_sha256 sha256;
    const size_t depth = CTZ(nbits);
    unsigned char commit[32] = {0};
    unsigned char randomizer61[32] = {0};  /* randomizer for eq (61) so we can add it to eq (62) to save a separate multiexp */
    secp256k1_bulletproof_vfy_ecmult_context ecmult_data;
    int overflow;
    secp256k1_scalar taux, mu, a, b;
    secp256k1_ge age, sge;
    secp256k1_ge lpt[SECP256K1_BULLETPROOF_MAX_DEPTH];  /* TODO we could save some stack by passing the raw proof data into the inner-product callback */
    secp256k1_ge rpt[SECP256K1_BULLETPROOF_MAX_DEPTH];
    size_t i;

    /* sanity-check input */
    if (POPCOUNT(nbits) != 1 || nbits > MAX_NBITS) {
        return 0;
    }
    if (plen != (9 + 2*depth) * 32 + (4 + 2*depth + 7) / 8) {
        return 0;
    }
    if (depth > SECP256K1_BULLETPROOF_MAX_DEPTH || plen > SECP256K1_BULLETPROOF_MAX_PROOF) {
        return 0;
    }

    /* Commit to all input data: pedersen commit, asset generator, extra_commit */
    secp256k1_bulletproof_update_commit(commit, commitp, genp);
    if (extra_commit != NULL) {
        secp256k1_sha256_initialize(&sha256);
        secp256k1_sha256_write(&sha256, commit, 32);
        secp256k1_sha256_write(&sha256, extra_commit, extra_commit_len);
        secp256k1_sha256_finalize(&sha256, commit);
    }

    /* Compute y, z, x */
    secp256k1_bulletproof_deserialize_point(&age, &proof[160], 0, 4 + 2*depth);
    secp256k1_bulletproof_deserialize_point(&sge, &proof[160], 1, 4 + 2*depth);

    secp256k1_bulletproof_update_commit(commit, &age, &sge);
    secp256k1_scalar_set_b32(&ecmult_data.y, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&ecmult_data.y)) {
        return 0;
    }
    secp256k1_bulletproof_update_commit(commit, &age, &sge);
    secp256k1_scalar_set_b32(&ecmult_data.z, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&ecmult_data.z)) {
        return 0;
    }

    secp256k1_bulletproof_deserialize_point(&ecmult_data.t1, &proof[160], 2, 4 + 2*depth);
    secp256k1_bulletproof_deserialize_point(&ecmult_data.t2, &proof[160], 3, 4 + 2*depth);

    secp256k1_bulletproof_update_commit(commit, &ecmult_data.t1, &ecmult_data.t2);
    secp256k1_scalar_set_b32(&ecmult_data.x, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&ecmult_data.x)) {
        return 0;
    }

    /* compute exponent offsets */
    ecmult_data.mul_by = ecmult_data.y;
    secp256k1_scalar_inverse_var(&ecmult_data.yinv, &ecmult_data.y);  /* TODO somehow batch this w the inner-product argument inverse */
    secp256k1_scalar_sqr(&ecmult_data.zsq, &ecmult_data.z);
    secp256k1_scalar_negate(&ecmult_data.negz, &ecmult_data.z);

    /* Update commit with remaining data for the inner product prof */
    secp256k1_sha256_initialize(&sha256);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_sha256_write(&sha256, &proof[0], 96);
    secp256k1_sha256_finalize(&sha256, commit);

    secp256k1_sha256_initialize(&sha256);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_sha256_finalize(&sha256, randomizer61);
    secp256k1_scalar_set_b32(&ecmult_data.randomizer61, randomizer61, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&ecmult_data.randomizer61)) {
        return 0;
    }

    /* Deserialize everything else */
    for (i = 0; i < depth; i++) {
        secp256k1_bulletproof_deserialize_point(&lpt[i], &proof[160], 4 + i, 4 + 2*depth);
        secp256k1_bulletproof_deserialize_point(&rpt[i], &proof[160], 4 + i + depth, 4 + 2*depth);
    }
    secp256k1_scalar_set_b32(&ecmult_data.t, &proof[0], &overflow);
    if (overflow || secp256k1_scalar_is_zero(&ecmult_data.t)) {
        return 0;
    }
    secp256k1_scalar_set_b32(&taux, &proof[32], &overflow);
    if (overflow || secp256k1_scalar_is_zero(&taux)) {
        return 0;
    }
    secp256k1_scalar_set_b32(&mu, &proof[64], &overflow);
    if (overflow || secp256k1_scalar_is_zero(&mu)) {
        return 0;
    }
    secp256k1_scalar_set_b32(&a, &proof[96], &overflow);
    if (overflow || secp256k1_scalar_is_zero(&a)) {
	    return 0;
    }
    secp256k1_scalar_set_b32(&b, &proof[128], &overflow);
    if (overflow || secp256k1_scalar_is_zero(&b)) {
        return 0;
    }

    /* Verify inner product proof */
    ecmult_data.parity = 0;
    ecmult_data.s = sge;
    ecmult_data.n = nbits;
    ecmult_data.count = 0;
    ecmult_data.asset = genp;
    ecmult_data.commit = commitp;
    secp256k1_scalar_mul(&taux, &taux, &ecmult_data.randomizer61);
    secp256k1_scalar_add(&mu, &mu, &taux);
    return secp256k1_bulletproof_inner_product_verify_impl(ecmult_ctx, scratch, geng, genh, &ecmult_data.t, &age, &mu, secp256k1_bulletproof_vfy_ecmult_callback, (void *) &ecmult_data, 5, &a, &b, lpt, rpt, depth, commit);
}

typedef struct {
    secp256k1_rfc6979_hmac_sha256 rng;
    secp256k1_scalar y;
    secp256k1_scalar z;
    secp256k1_scalar yn;
    secp256k1_scalar z22n;
    uint64_t val;
} secp256k1_bulletproof_lr_generator;

static void secp256k1_lr_generator_init(secp256k1_bulletproof_lr_generator *generator, const secp256k1_rfc6979_hmac_sha256 *rng, const secp256k1_scalar *y, const secp256k1_scalar *z, uint64_t val) {
    memcpy(&generator->rng, rng, sizeof(*rng));
    generator->y = *y;
    generator->z = *z;
    secp256k1_scalar_set_int(&generator->yn, 1);
    secp256k1_scalar_sqr(&generator->z22n, z);
    generator->val = val;
}

static void secp256k1_lr_generator_finalize(secp256k1_bulletproof_lr_generator *generator) {
    secp256k1_rfc6979_hmac_sha256_finalize(&generator->rng);
    generator->val = 0;
}

static void secp256k1_lr_generate(secp256k1_bulletproof_lr_generator *generator, secp256k1_scalar *lout, secp256k1_scalar *rout, const secp256k1_scalar *x) {
    secp256k1_scalar sl, sr;
    secp256k1_scalar negz;

    secp256k1_bulletproof_genrand_pair(&generator->rng, &sl, &sr);
    secp256k1_scalar_mul(&sl, &sl, x);
    secp256k1_scalar_mul(&sr, &sr, x);

    secp256k1_scalar_set_int(lout, generator->val & 1);
    secp256k1_scalar_negate(&negz, &generator->z);
    secp256k1_scalar_add(lout, lout, &negz);
    secp256k1_scalar_add(lout, lout, &sl);

    secp256k1_scalar_set_int(rout, 1 - (generator->val & 1));
    secp256k1_scalar_negate(rout, rout);
    secp256k1_scalar_add(rout, rout, &generator->z);
    secp256k1_scalar_add(rout, rout, &sr);
    secp256k1_scalar_mul(rout, rout, &generator->yn);
    secp256k1_scalar_add(rout, rout, &generator->z22n);

    generator->val >>= 1;
    secp256k1_scalar_mul(&generator->yn, &generator->yn, &generator->y);
    secp256k1_scalar_add(&generator->z22n, &generator->z22n, &generator->z22n);
}

typedef struct {
    secp256k1_scalar yinv;
    secp256k1_scalar x;
    secp256k1_scalar mul;
    secp256k1_scalar cache;
    secp256k1_bulletproof_lr_generator lr_gen;
    const secp256k1_ge *geng;
    const secp256k1_ge *genh;
} secp256k1_bulletproof_abgh_data;

static int secp256k1_bulletproof_abgh_callback(secp256k1_scalar *sc, secp256k1_ge *pt, size_t idx, void *data) {
    secp256k1_bulletproof_abgh_data *ctx = (secp256k1_bulletproof_abgh_data *) data;
    const int is_g = idx % 2 == 0;

    if (is_g) {
        secp256k1_lr_generate(&ctx->lr_gen, sc, &ctx->cache, &ctx->x);
        *pt = ctx->geng[idx / 2];
    } else {
        /* Map h -> h' (eqn 59) */
        secp256k1_gej genhj;
        secp256k1_ecmult_const(&genhj, &ctx->genh[idx / 2], &ctx->mul, 256);
        *sc = ctx->cache;
        secp256k1_ge_set_gej(pt, &genhj);

        secp256k1_scalar_mul(&ctx->mul, &ctx->mul, &ctx->yinv);
    }

    return 1;
}

/* Proof format: t, tau_x, mu, a, b, A, S, T_1, T_2, {L_i}, {R_i}
 *               5 scalar + [4 + 2log(n)] ge
 *
 * The non-bold `h` in the Bulletproofs paper corresponds to our secp256k1_ge_const_g
 * while the non-bold `g` corresponds to the asset type `genp`.
 */
static int secp256k1_bulletproof_rangeproof_prove_impl(const secp256k1_ecmult_gen_context *ecmult_gen_ctx, const secp256k1_ecmult_context *ecmult_ctx, secp256k1_scratch *scratch, unsigned char *proof, size_t *plen, const size_t nbits, const uint64_t value, const secp256k1_scalar *blind, const secp256k1_ge *commitp, const secp256k1_ge *genp, const secp256k1_ge *geng, const secp256k1_ge *genh, const unsigned char *nonce, const unsigned char *extra_commit, size_t extra_commit_len) {
    secp256k1_bulletproof_lr_generator lr_gen;
    secp256k1_bulletproof_abgh_data abgh_data;
    secp256k1_scalar zero;
    secp256k1_sha256 sha256;
    const size_t depth = CTZ(nbits);
    unsigned char commit[32] = {0};
    secp256k1_scalar alpha, rho;
    secp256k1_scalar t, t0, t1, t2;
    secp256k1_scalar tau1, tau2, taux, mu;
    secp256k1_gej tj[2];      /* T_1, T_2 */
    secp256k1_scalar y;
    secp256k1_scalar z, zsq;
    secp256k1_scalar x, xsq;
    secp256k1_scalar tmps;
    secp256k1_gej aj, sj;
    secp256k1_gej tmpj;
    size_t i;
    int overflow;
    unsigned char rngseed[64];
    secp256k1_rfc6979_hmac_sha256 rng;
    /* inner product proof variables */
    secp256k1_scalar a, b;
    secp256k1_ge out_pt[4 + 2*SECP256K1_BULLETPROOF_MAX_DEPTH];

    if (POPCOUNT(nbits) != 1 || nbits > MAX_NBITS) {
        return 0;
    }
    if (nbits < 64 && value >= (1ull << nbits)) {
        return 0;
    }
    if (*plen < (9 + 2*depth) * 32 + (4 + 2*depth + 7) / 8) {
        return 0;
    } else {
        *plen = (9 + 2*depth) * 32 + (4 + 2*depth + 7) / 8;
    }

    secp256k1_scalar_clear(&zero);

    /* Commit to all input data: pedersen commit, asset generator, extra_commit */
    secp256k1_bulletproof_update_commit(commit, commitp, genp);
    if (extra_commit != NULL) {
        secp256k1_sha256_initialize(&sha256);
        secp256k1_sha256_write(&sha256, commit, 32);
        secp256k1_sha256_write(&sha256, extra_commit, extra_commit_len);
        secp256k1_sha256_finalize(&sha256, commit);
    }

    memcpy(rngseed, nonce, 32);
    memcpy(rngseed+32, commit, 32);
    secp256k1_rfc6979_hmac_sha256_initialize(&rng, rngseed, 64);
    memset(rngseed, 0, 32);
    secp256k1_bulletproof_genrand_pair(&rng, &alpha, &rho);
    secp256k1_bulletproof_genrand_pair(&rng, &tau1, &tau2);

    /* Compute A and S */
    lr_gen.rng = rng;
    secp256k1_ecmult_gen(ecmult_gen_ctx, &aj, &alpha);
    secp256k1_ecmult_gen(ecmult_gen_ctx, &sj, &rho);
    for (i = 0; i < nbits; i++) {
        secp256k1_scalar sl, sr;
        size_t al = !!(value & (1ull << i));
        secp256k1_ge aterm = genh[i];
        secp256k1_ge sterm;
        secp256k1_gej stermj;

        secp256k1_bulletproof_genrand_pair(&lr_gen.rng, &sl, &sr);

        secp256k1_ge_neg(&aterm, &aterm);
        secp256k1_fe_cmov(&aterm.x, &geng[i].x, al);
        secp256k1_fe_cmov(&aterm.y, &geng[i].y, al);

        secp256k1_gej_add_ge(&aj, &aj, &aterm);

        secp256k1_ecmult_const(&stermj, &geng[i], &sl, 256);
        secp256k1_ge_set_gej(&sterm, &stermj);
        secp256k1_gej_add_ge(&sj, &sj, &sterm);
        secp256k1_ecmult_const(&stermj, &genh[i], &sr, 256);
        secp256k1_ge_set_gej(&sterm, &stermj);
        secp256k1_gej_add_ge(&sj, &sj, &sterm);
    }
    secp256k1_rfc6979_hmac_sha256_finalize(&lr_gen.rng);

    /* get challenges y and z */
    secp256k1_ge_set_gej(&out_pt[0], &aj);
    secp256k1_ge_set_gej(&out_pt[1], &sj);

    secp256k1_bulletproof_update_commit(commit, &out_pt[0], &out_pt[1]);
    secp256k1_scalar_set_b32(&y, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&y)) {
        return 0;
    }
    secp256k1_bulletproof_update_commit(commit, &out_pt[0], &out_pt[1]); /* TODO rehashing A and S to get a second challenge is overkill */
    secp256k1_scalar_set_b32(&z, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&z)) {
        return 0;
    }
    secp256k1_scalar_sqr(&zsq, &z);

    /* Compute coefficients t0, t1, t2 of the <l, r> polynomial */
    /* t0 = l(0) dot r(0) */
    secp256k1_lr_generator_init(&lr_gen, &rng, &y, &z, value);
    secp256k1_scalar_clear(&t0);
    for (i = 0; i < nbits; i++) {
        secp256k1_scalar l, r;
        secp256k1_lr_generate(&lr_gen, &l, &r, &zero);
        secp256k1_scalar_mul(&l, &l, &r);
        secp256k1_scalar_add(&t0, &t0, &l);
    }
    secp256k1_lr_generator_finalize(&lr_gen);

    /* A = t0 + t1 + t2 = l(1) dot r(1) */
    secp256k1_lr_generator_init(&lr_gen, &rng, &y, &z, value);
    secp256k1_scalar_clear(&t1);
    for (i = 0; i < nbits; i++) {
        secp256k1_scalar one;
        secp256k1_scalar l, r;
        secp256k1_scalar_set_int(&one, 1);
        secp256k1_lr_generate(&lr_gen, &l, &r, &one);
        secp256k1_scalar_mul(&l, &l, &r);
        secp256k1_scalar_add(&t1, &t1, &l);
    }
    secp256k1_lr_generator_finalize(&lr_gen);

    /* B = t0 - t1 + t2 = l(-1) dot r(-1) */
    secp256k1_lr_generator_init(&lr_gen, &rng, &y, &z, value);
    secp256k1_scalar_clear(&t2);
    for (i = 0; i < nbits; i++) {
        secp256k1_scalar negone;
        secp256k1_scalar l, r;
        secp256k1_scalar_set_int(&negone, 1);
        secp256k1_scalar_negate(&negone, &negone);
        secp256k1_lr_generate(&lr_gen, &l, &r, &negone);
        secp256k1_scalar_mul(&l, &l, &r);
        secp256k1_scalar_add(&t2, &t2, &l);
    }
    secp256k1_lr_generator_finalize(&lr_gen);

    /* t1 = (A - B)/2 */
    secp256k1_scalar_set_int(&tmps, 2);
    secp256k1_scalar_inverse_var(&tmps, &tmps);
    secp256k1_scalar_negate(&t2, &t2);
    secp256k1_scalar_add(&t1, &t1, &t2);
    secp256k1_scalar_mul(&t1, &t1, &tmps);

    /* t2 = -(-B + t0) + t1 */
    secp256k1_scalar_add(&t2, &t2, &t0);
    secp256k1_scalar_negate(&t2, &t2);
    secp256k1_scalar_add(&t2, &t2, &t1);

    /* Compute Ti = t_i*A + tau_i*G for i = 1,2 */
    secp256k1_gej_set_ge(&tmpj, genp);
    secp256k1_ecmult(ecmult_ctx, &tj[0], &tmpj, &t1, &tau1);
    secp256k1_ecmult(ecmult_ctx, &tj[1], &tmpj, &t2, &tau2);
    secp256k1_ge_set_gej(&out_pt[2], &tj[0]);
    secp256k1_ge_set_gej(&out_pt[3], &tj[1]);

    /* get challenge x */
    secp256k1_bulletproof_update_commit(commit, &out_pt[2], &out_pt[3]);
    secp256k1_scalar_set_b32(&x, commit, &overflow);
    if (overflow || secp256k1_scalar_is_zero(&x)) {
        return 0;
    }
    secp256k1_scalar_sqr(&xsq, &x);

    /* compute tau_x, mu and t */
    secp256k1_scalar_mul(&taux, &tau1, &x);
    secp256k1_scalar_mul(&tmps, &tau2, &xsq);
    secp256k1_scalar_add(&taux, &taux, &tmps);
    secp256k1_scalar_mul(&tmps, &zsq, blind);
    secp256k1_scalar_add(&taux, &taux, &tmps);

    secp256k1_scalar_mul(&mu, &rho, &x);
    secp256k1_scalar_add(&mu, &mu, &alpha);

    secp256k1_scalar_mul(&tmps, &t2, &xsq);
    secp256k1_scalar_mul(&t, &t1, &x);
    secp256k1_scalar_add(&t, &t, &tmps);
    secp256k1_scalar_add(&t, &t, &t0);

    /* Negate taux and mu so the verifier doesn't have to */
    secp256k1_scalar_negate(&taux, &taux);
    secp256k1_scalar_negate(&mu, &mu);

    /* Mix these scalars into the hash so the input to the inner product proof is fixed */
    secp256k1_sha256_initialize(&sha256);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_scalar_get_b32(commit, &t);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_scalar_get_b32(commit, &taux);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_scalar_get_b32(commit, &mu);
    secp256k1_sha256_write(&sha256, commit, 32);
    secp256k1_sha256_finalize(&sha256, commit);

    /* Compute l and r, do inner product proof */
    secp256k1_scalar_inverse_var(&abgh_data.yinv, &y);
    abgh_data.x = x;
    secp256k1_scalar_set_int(&abgh_data.mul, 1);
    abgh_data.geng = geng;
    abgh_data.genh = genh;
    secp256k1_lr_generator_init(&abgh_data.lr_gen, &rng, &y, &z, value);
    secp256k1_bulletproof_inner_product_prove_impl(ecmult_ctx, scratch, &a, &b, &out_pt[4], &out_pt[4 + depth], depth, secp256k1_bulletproof_abgh_callback, (void *) &abgh_data, commit);
    secp256k1_lr_generator_finalize(&abgh_data.lr_gen);

    /* Encode everything */
    secp256k1_scalar_get_b32(&proof[0], &t);
    secp256k1_scalar_get_b32(&proof[32], &taux);
    secp256k1_scalar_get_b32(&proof[64], &mu);
    secp256k1_scalar_get_b32(&proof[96], &a);
    secp256k1_scalar_get_b32(&proof[128], &b);
    secp256k1_bulletproof_serialize_points(&proof[160], out_pt, 4 + 2*depth);

    secp256k1_rfc6979_hmac_sha256_finalize(&rng);

    return 1;
}
#endif
