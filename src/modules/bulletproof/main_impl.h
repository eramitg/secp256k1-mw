/**********************************************************************
 * Copyright (c) 2017 Andrew Poelstra                                 *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_BULLETPROOF_MAIN_IMPL
#define SECP256K1_MODULE_BULLETPROOF_MAIN_IMPL

#include "group.h"
#include "scalar.h"

#include "modules/rangeproof/main_impl.h"
#include "modules/rangeproof/pedersen_impl.h"

#include "modules/bulletproof/generators.h"
#include "modules/bulletproof/parser_impl.h"
#include "modules/bulletproof/inner_product_impl.h"
#include "modules/bulletproof/circuit_impl.h"
#include "modules/bulletproof/rangeproof_impl.h"
#include "modules/bulletproof/util.h"

int secp256k1_bulletproof_rangeproof_verify(const secp256k1_context* ctx, secp256k1_scratch_space *scratch, const unsigned char *proof, size_t plen,
 const secp256k1_pedersen_commitment* commit, size_t n_commits, size_t nbits, const secp256k1_generator* gen, const unsigned char *extra_commit, size_t extra_commit_len) {
    size_t i;
    secp256k1_ge genp;
    secp256k1_ge commitp[100];
    const secp256k1_ge *commitp_ptr = commitp;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(scratch != NULL);
    ARG_CHECK(commit != NULL);
    ARG_CHECK(gen != NULL);
    ARG_CHECK(n_commits <= sizeof(commitp) / sizeof(commitp[0]));
    ARG_CHECK(extra_commit != NULL || extra_commit_len == 0);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));

    secp256k1_generator_load(&genp, gen);
    for (i = 0; i < n_commits; i++) {
        secp256k1_pedersen_commitment_load(&commitp[i], &commit[i]);
    }

    return secp256k1_bulletproof_rangeproof_verify_impl(&ctx->ecmult_ctx, scratch, &proof, &plen, 1, nbits, &commitp_ptr, n_commits, &genp, &secp256k1_ge_const_gi[0], &secp256k1_ge_const_gi[64], extra_commit, extra_commit_len);
}

int secp256k1_bulletproof_rangeproof_verify_multi(const secp256k1_context* ctx, secp256k1_scratch_space *scratch, const unsigned char *proof, size_t plen, size_t n_proofs, const secp256k1_pedersen_commitment* commit, size_t n_commits, size_t nbits, const secp256k1_generator* gen, const unsigned char *extra_commit, size_t extra_commit_len) {
    const unsigned char *proof_ptr[MAX_BATCH_QTY];
    size_t plens[MAX_BATCH_QTY];
    secp256k1_ge genp;
    secp256k1_ge commitp[100];
    const secp256k1_ge *commitp_ptr[MAX_BATCH_QTY];
    size_t i;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(scratch != NULL);
    ARG_CHECK(commit != NULL);
    ARG_CHECK(gen != NULL);
    ARG_CHECK(extra_commit != NULL || extra_commit_len == 0);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));

    secp256k1_generator_load(&genp, gen);
for (i = 0; i < n_commits; i++) {
    secp256k1_pedersen_commitment_load(&commitp[i], &commit[i]);
}
for (i = 0; i < 100; i++) {
    proof_ptr[i] = proof;
    commitp_ptr[i] = commitp;
    plens[i] = plen;
}

    return secp256k1_bulletproof_rangeproof_verify_impl(&ctx->ecmult_ctx, scratch, proof_ptr, plens, n_proofs, nbits, commitp_ptr, n_commits, &genp, &secp256k1_ge_const_gi[0], &secp256k1_ge_const_gi[64], extra_commit, extra_commit_len);
}

int secp256k1_bulletproof_rangeproof_prove(const secp256k1_context* ctx, secp256k1_scratch_space *scratch, unsigned char *proof, size_t *plen, uint64_t *value, const unsigned char **blind, size_t n_commits,
 const secp256k1_generator* gen, size_t nbits, const unsigned char *nonce, const unsigned char *extra_commit, size_t extra_commit_len) {
    secp256k1_ge commitp[100]; /* TODO choose a sane limit */
    secp256k1_scalar blinds[100];
    secp256k1_ge genp;
    size_t i;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(scratch != NULL);
    ARG_CHECK(proof != NULL);
    ARG_CHECK(plen != NULL);
    ARG_CHECK(blind != NULL);
    ARG_CHECK(gen != NULL);
    ARG_CHECK(nonce != NULL);
    ARG_CHECK(n_commits <= sizeof(commitp) / sizeof(commitp[0]));
    ARG_CHECK(nbits <= 64);
    if (nbits < 64) {
        for (i = 0; i < n_commits; i++) {
            ARG_CHECK(value[i] < (1ull << nbits));
            ARG_CHECK(blind[i] != NULL);
        }
    }
    ARG_CHECK(extra_commit != NULL || extra_commit_len == 0);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));

    secp256k1_generator_load(&genp, gen);

    for (i = 0; i < n_commits; i++) {
        int overflow;
        secp256k1_gej commitj;
        secp256k1_scalar_set_b32(&blinds[i], blind[i], &overflow);
        if (overflow || secp256k1_scalar_is_zero(&blinds[i])) {
            return 0;
        }
        secp256k1_pedersen_ecmult(&ctx->ecmult_gen_ctx, &commitj, &blinds[i], value[i], &genp);
        secp256k1_ge_set_gej(&commitp[i], &commitj);
    }

    return secp256k1_bulletproof_rangeproof_prove_impl(&ctx->ecmult_gen_ctx, &ctx->ecmult_ctx, scratch,
        proof, plen, nbits, value, blinds, commitp, n_commits, &genp, &secp256k1_ge_const_gi[0], &secp256k1_ge_const_gi[64], nonce, extra_commit, extra_commit_len);
}

secp256k1_bulletproof_circuit *secp256k1_circuit_parse(const secp256k1_context *ctx, const char *description) {
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(description != NULL);
    return secp256k1_parse_circuit(ctx, description);
}

/* Build a dummy circuit with N gates and 2N constraints of the for*/
secp256k1_bulletproof_circuit *secp256k1_circuit_dummy(const secp256k1_context *ctx, size_t n_gates) {
    size_t i;
    secp256k1_bulletproof_circuit *ret = (secp256k1_bulletproof_circuit*)checked_malloc(&ctx->error_callback, sizeof(*ret));
    ret->n_gates = n_gates;
    ret->n_constraints = 2 * n_gates;
    ret->n_commits = 0;

    ret->wl = (secp256k1_bulletproof_wmatrix_row *)checked_malloc(&ctx->error_callback, ret->n_gates * sizeof(*ret->wl));
    ret->wr = (secp256k1_bulletproof_wmatrix_row *)checked_malloc(&ctx->error_callback, ret->n_gates * sizeof(*ret->wr));
    ret->wo = (secp256k1_bulletproof_wmatrix_row *)checked_malloc(&ctx->error_callback, ret->n_gates * sizeof(*ret->wo));
    ret->wv = (secp256k1_bulletproof_wmatrix_row *)checked_malloc(&ctx->error_callback, ret->n_commits * sizeof(*ret->wv));
    ret->c = (secp256k1_scalar *)checked_malloc(&ctx->error_callback, ret->n_constraints * sizeof(*ret->wl));

    ret->scratch = (secp256k1_scalar *)checked_malloc(&ctx->error_callback, ret->n_constraints * sizeof(*ret->scratch));

    memset(ret->wl, 0, ret->n_gates * sizeof(*ret->wl));
    memset(ret->wr, 0, ret->n_gates * sizeof(*ret->wr));
    memset(ret->wo, 0, ret->n_gates * sizeof(*ret->wo));
    memset(ret->wv, 0, ret->n_commits * sizeof(*ret->wv));
    memset(ret->c, 0, ret->n_constraints * sizeof(*ret->c));

    for (i = 0; i < ret->n_gates; i++) {
        ret->wl[i].size = 1;
        ret->wl[i].entry = checked_malloc(&ctx->error_callback, 1 * sizeof(*ret->wl[0].entry));
        ret->wl[i].entry[0].idx = 2*i;
        ret->wl[i].entry[0].special = 0;
        secp256k1_scalar_set_int(&ret->wl[i].entry[0].scal, i + 5);

        ret->wr[i].size = 1;
        ret->wr[i].entry = checked_malloc(&ctx->error_callback, 1 * sizeof(*ret->wl[0].entry));
        ret->wr[i].entry[0].idx = 2*i+1;
        ret->wr[i].entry[0].special = 0;
        secp256k1_scalar_set_int(&ret->wr[i].entry[0].scal, i + 3);

        ret->wo[i].size = 2;
        ret->wo[i].entry = checked_malloc(&ctx->error_callback, 2 * sizeof(*ret->wl[0].entry));
        ret->wo[i].entry[0].idx = 2*i;
        ret->wo[i].entry[0].special = 0;
        secp256k1_scalar_set_int(&ret->wo[i].entry[0].scal, i + 9);
        ret->wo[i].entry[1].idx = 2*i+1;
        ret->wo[i].entry[1].special = 0;
        secp256k1_scalar_set_int(&ret->wo[i].entry[1].scal, i + 7);
    }

    return ret;
}

void *secp256k1_bulletproof_allocate_gens(const secp256k1_context *ctx, size_t n_gens) {
    size_t i;
    secp256k1_ge *gens = (secp256k1_ge *) checked_malloc(&ctx->error_callback, sizeof(secp256k1_ge) * n_gens);

    for (i = 0; i < n_gens; i++) {
       secp256k1_generator tmpgen;
       unsigned char commit[32] = { 0 };
       commit[0] = i;
       commit[1] = i >> 8;
       commit[2] = i >> 16;
       commit[3] = i >> 24;
       commit[4] = i >> 32;
       commit[5] = i >> 40;

       CHECK(secp256k1_generator_generate(ctx, &tmpgen, commit));
       secp256k1_generator_load(&gens[i], &tmpgen);
    }

    return (void *) gens;
}

int secp256k1_bulletproof_circuit_prove_dummy(const secp256k1_context* ctx, secp256k1_scratch_space *scratch, unsigned char *proof, size_t *plen, secp256k1_bulletproof_circuit *circ, unsigned char *nonce, const void *generators) {
    int result;
    secp256k1_scalar *al = (secp256k1_scalar *)checked_malloc(&ctx->error_callback, circ->n_gates * sizeof(*al));
    secp256k1_scalar *ar = (secp256k1_scalar *)checked_malloc(&ctx->error_callback, circ->n_gates * sizeof(*al));
    secp256k1_scalar *ao = (secp256k1_scalar *)checked_malloc(&ctx->error_callback, circ->n_gates * sizeof(*al));
    secp256k1_ge *gens = (secp256k1_ge *) generators;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(scratch != NULL);
    ARG_CHECK(proof != NULL);
    ARG_CHECK(plen != NULL);
    ARG_CHECK(circ != NULL);
    ARG_CHECK(nonce != NULL);

    memset(al, 0, circ->n_gates * sizeof(*al));
    memset(ar, 0, circ->n_gates * sizeof(*al));
    memset(ao, 0, circ->n_gates * sizeof(*al));

    result = secp256k1_bulletproof_relation66_prove_impl(
        &ctx->ecmult_ctx,
        scratch,
        proof, plen,
        al, ar, ao, circ->n_gates,
        NULL, NULL, 0,
        &secp256k1_ge_const_g2,
        circ,
        &gens[0], &gens[circ->n_gates],
        nonce,
        NULL, 0
    );

    free(al);
    free(ar);
    free(ao);

    return result;
}

void secp256k1_circuit_destroy(const secp256k1_context *ctx, secp256k1_bulletproof_circuit *circ) {
    VERIFY_CHECK(ctx != NULL);
    secp256k1_circuit_destroy_impl(circ);
}

int secp256k1_bulletproof_circuit_prove(const secp256k1_context* ctx, secp256k1_scratch_space *scratch, unsigned char *proof, size_t *plen, secp256k1_bulletproof_circuit *circ, unsigned char *nonce, const void *generators) {
    secp256k1_ge *gens = (secp256k1_ge *) generators;
#include "circuits/jubjub-3072.assn"

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(scratch != NULL);
    ARG_CHECK(proof != NULL);
    ARG_CHECK(plen != NULL);
    ARG_CHECK(circ != NULL);
    ARG_CHECK(nonce != NULL);

    return secp256k1_bulletproof_relation66_prove_impl(
        &ctx->ecmult_ctx,
        scratch,
        proof, plen,
        incl_al, incl_ar, incl_ao, circ->n_gates,
        NULL, NULL, 0,
        &secp256k1_ge_const_g2,
        circ,
        &gens[0], &gens[circ->n_gates],
        nonce,
        NULL, 0
    );
}

int secp256k1_bulletproof_circuit_verify(const secp256k1_context* ctx, secp256k1_scratch_space *scratch, const unsigned char *proof, size_t plen, secp256k1_bulletproof_circuit *circ, const void *generators) {
    secp256k1_ge *gens = (secp256k1_ge *) generators;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(scratch != NULL);
    ARG_CHECK(proof != NULL);
    ARG_CHECK(circ != NULL);

    return secp256k1_bulletproof_relation66_verify_impl(
        &ctx->ecmult_ctx,
        scratch,
        &proof, &plen, 1,
        NULL, 0,
        &secp256k1_ge_const_g2,
        &circ,
        &gens[0], &gens[circ->n_gates],
        NULL, 0
    );
}

int secp256k1_bulletproof_circuit_verify_multi(const secp256k1_context* ctx, secp256k1_scratch_space *scratch, const unsigned char *proof, size_t plen, size_t n_proofs, secp256k1_bulletproof_circuit **circ, const void *generators) {
    secp256k1_ge *gens = (secp256k1_ge *) generators;
    const unsigned char *proof_ptr[MAX_BATCH_QTY];
    size_t plens[MAX_BATCH_QTY];
    size_t i;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(scratch != NULL);
    ARG_CHECK(proof != NULL);
    ARG_CHECK(circ != NULL);

    for (i = 0; i < n_proofs; i++) {
        proof_ptr[i] = proof;
        plens[i] = plen;
    }

    return secp256k1_bulletproof_relation66_verify_impl(
        &ctx->ecmult_ctx,
        scratch,
        proof_ptr, plens, n_proofs,
        NULL, 0,
        &secp256k1_ge_const_g2,
        circ,
        &gens[0], &gens[circ[0]->n_gates],
        NULL, 0
    );
}

#endif
