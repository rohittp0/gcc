//
// Created by Rohit T P on 29/08/23.
//
#define IN_TARGET_CODE 1
#define INCLUDE_STRING
#define VSET_TOLERATE 2
#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "backend.h"
#include "rtl.h"
#include "regs.h"
#include "insn-config.h"
#include "insn-attr.h"
#include "recog.h"
#include "output.h"
#include "alias.h"
#include "tree.h"
#include "stringpool.h"
#include "attribs.h"
#include "varasm.h"
#include "stor-layout.h"
#include "calls.h"
#include "function.h"
#include "explow.h"
#include "memmodel.h"
#include "emit-rtl.h"
#include "reload.h"
#include "tm_p.h"
#include "target.h"
#include "basic-block.h"
#include "expr.h"
#include "optabs.h"
#include "bitmap.h"
#include "df.h"
#include "diagnostic.h"
#include "builtins.h"
#include "predict.h"
#include "tree-pass.h"
#include "opts.h"
#include "langhooks.h"
#include "rtl-iter.h"
#include "gimple.h"
#include "cfghooks.h"
#include "cfgloop.h"
#include "fold-const.h"
#include "gimple-iterator.h"
#include "tree-ssa-loop-niter.h"
#include "riscv-vector.h"

opt_machine_mode riscv_vector_data_mode (scalar_mode inner_mode, poly_uint64 nunits)
{
//    enum mode_class mclass TODO: Uncomment and face the errors
//            = (is_a<scalar_float_mode> (inner_mode) ? MODE_VECTOR_FLOAT
//                                                    : MODE_VECTOR_INT);
//    machine_mode mode;
//    FOR_EACH_MODE_IN_CLASS (mode, mclass)
//    if (inner_mode == GET_MODE_INNER (mode)
//        && known_eq (nunits, GET_MODE_NUNITS (mode))
//        && riscv_vector_data_mode_p (mode) && !riscv_tuple_mode_p (mode))
//        return mode;
    return opt_machine_mode ();
}

void riscv_vector_expand_poly_move (machine_mode mode, rtx dest, rtx clobber, rtx src)
{
    poly_int64 value = rtx_to_poly_int64 (src);
    int offset = value.coeffs[0];
    int factor = value.coeffs[1];
    int vlenb = BYTES_PER_RISCV_VECTOR.coeffs[1];
    int div_factor = 0;

    if (BYTES_PER_RISCV_VECTOR.is_constant ())
    {
        gcc_assert (value.is_constant ());
        riscv_emit_move (dest, GEN_INT (value.to_constant ()));
        return;
    }
    else if ((factor % vlenb) == 0)
        riscv_expand_quotient (factor / vlenb, mode, clobber, dest);
    else if ((factor % (vlenb / 2)) == 0)
    {
        riscv_expand_quotient (factor / (vlenb / 2), mode, clobber, dest);
        div_factor = 2;
    }
    else if ((factor % (vlenb / 4)) == 0)
    {
        riscv_expand_quotient (factor / (vlenb / 4), mode, clobber, dest);
        div_factor = 4;
    }
    else if ((factor % (vlenb / 8)) == 0)
    {
        riscv_expand_quotient (factor / (vlenb / 8), mode, clobber, dest);
        div_factor = 8;
    }
    else if ((factor % (vlenb / 16)) == 0)
    {
        riscv_expand_quotient (factor / (vlenb / 16), mode, clobber, dest);
        div_factor = 16;
    }
    else
        gcc_unreachable ();

    if (div_factor != 0)
    {
        if (GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode))
            emit_insn (
                    gen_rtx_SET (dest,
                                 gen_rtx_ASHIFTRT (mode, dest,
                                                   GEN_INT (exact_log2 (div_factor)))));
        else
        {
            /* We should use SImode to simulate DImode shift. */
            /* prologue and epilogue can not go through this condition. */
            gcc_assert (can_create_pseudo_p ());
            rtx reg = gen_reg_rtx (Pmode);
            emit_insn (
                    gen_rtx_SET (reg,
                                 gen_rtx_ASHIFT (Pmode, gen_highpart (Pmode, dest),
                                                 GEN_INT (GET_MODE_BITSIZE (Pmode)
                                                          - exact_log2 (div_factor)))));
            emit_insn (
                    gen_rtx_SET (gen_lowpart (Pmode, dest),
                                 gen_rtx_LSHIFTRT (Pmode, gen_lowpart (Pmode, dest),
                                                   GEN_INT (exact_log2 (div_factor)))));
            emit_insn (
                    gen_rtx_SET (gen_lowpart (Pmode, dest),
                                 gen_rtx_IOR (Pmode, reg, gen_lowpart (Pmode, dest))));
            emit_insn (
                    gen_rtx_SET (gen_highpart (Pmode, dest),
                                 gen_rtx_ASHIFTRT (Pmode, gen_highpart (Pmode, dest),
                                                   GEN_INT (exact_log2 (div_factor)))));
        }
    }

    HOST_WIDE_INT constant = offset - factor;

    if (constant == 0)
        return;
    else if (SMALL_OPERAND (constant))
    {
        if (GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode))
            emit_insn (
                    gen_rtx_SET (dest, gen_rtx_PLUS (mode, dest, GEN_INT (constant))));
        else
        {
            /* We should use SImode to simulate DImode addition. */
            /* prologue and epilogue can not go through this condition. */
            gcc_assert (can_create_pseudo_p ());
            rtx reg = gen_reg_rtx (Pmode);
            emit_insn (
                    gen_rtx_SET (reg, gen_rtx_PLUS (Pmode, gen_lowpart (Pmode, dest),
                                                    GEN_INT (constant))));
            emit_insn (
                    gen_rtx_SET (gen_lowpart (Pmode, dest),
                                 gen_rtx_LTU (Pmode, reg, gen_lowpart (Pmode, dest))));
            emit_insn (
                    gen_rtx_SET (gen_highpart (Pmode, dest),
                                 gen_rtx_PLUS (Pmode, gen_lowpart (Pmode, dest),
                                               gen_highpart (Pmode, dest))));
            riscv_emit_move (gen_lowpart (Pmode, dest), reg);
        }
    }
    else
        emit_insn (gen_rtx_SET (dest, riscv_add_offset (clobber, dest, constant)));
}

/* Implement while_len auto-vectorization pattern. */
void riscv_vector_expand_while_len (rtx *operands)
{
    poly_int64 offset;
    machine_mode mode;
    scalar_mode inner_mode;
    switch (INTVAL (operands[2]))
    {
        case 8:
            inner_mode = QImode;
            break;
        case 16:
            inner_mode = HImode;
            break;
        case 32:
            inner_mode = SImode;
            break;
        case 64:
            inner_mode = DImode;
            break;
        default:
            gcc_unreachable ();
    }

    gcc_assert (poly_int_rtx_p (operands[3], &offset));
    if (!riscv_vector_data_mode (inner_mode, offset).exists (&mode))
    {
        rtx clobber = gen_reg_rtx (Pmode);
        riscv_vector_expand_poly_move (Pmode, operands[0], clobber,
                                       gen_int_mode (offset, Pmode));
    }
}