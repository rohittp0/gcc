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

/* Note: clobber register holds the vlenb or 1/2 vlenb or 1/4 vlenb or 1/8 vlenb
 * value. */
/* Expand move for quotient.  */
static void riscv_expand_quotient (int quotient, machine_mode mode, rtx clobber_vlenb, rtx dest)
{
    if (quotient == 0)
    {
        riscv_emit_move (dest, GEN_INT (0));
        return;
    }

    bool is_neg = quotient < 0;
    quotient = abs (quotient);
    int log2 = exact_log2 (quotient);
    int vlenb = BYTES_PER_RISCV_VECTOR.coeffs[1];

    if (GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode)) {
        auto poly = poly_int64 (vlenb, vlenb);
        auto the_mode = gen_int_mode (poly, mode);
        auto ins = gen_rtx_SET(clobber_vlenb, the_mode);
        emit_insn(ins);
    }
    else
    {
        riscv_emit_move (gen_highpart (Pmode, clobber_vlenb), GEN_INT (0));
        emit_insn (gen_rtx_SET (gen_lowpart (Pmode, clobber_vlenb),
                                gen_int_mode (poly_int64 (vlenb, vlenb), Pmode)));
    }

    if (log2 == 0)
    {
        if (is_neg)
        {
            if (GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode))
                emit_insn (gen_rtx_SET (dest, gen_rtx_NEG (mode, clobber_vlenb)));
            else
            {
                /* We should use SImode to simulate DImode negation. */
                /* prologue and epilogue can not go through this condition. */
                gcc_assert (can_create_pseudo_p ());
                rtx reg = gen_reg_rtx (Pmode);
                riscv_emit_move (dest, clobber_vlenb);
                emit_insn (
                        gen_rtx_SET (reg, gen_rtx_NE (Pmode, gen_lowpart (Pmode, dest),
                                                      const0_rtx)));
                emit_insn (
                        gen_rtx_SET (gen_highpart (Pmode, dest),
                                     gen_rtx_NEG (Pmode, gen_highpart (Pmode, dest))));
                emit_insn (
                        gen_rtx_SET (gen_lowpart (Pmode, dest),
                                     gen_rtx_NEG (Pmode, gen_lowpart (Pmode, dest))));
                emit_insn (
                        gen_rtx_SET (gen_highpart (Pmode, dest),
                                     gen_rtx_MINUS (Pmode, gen_highpart (Pmode, dest),
                                                    reg)));
            }
        }
        else
            riscv_emit_move (dest, clobber_vlenb);
    }
    else if (log2 != -1
             && GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode))
    {
        gcc_assert (IN_RANGE (log2, 0, 31));

        if (is_neg)
        {
            emit_insn (gen_rtx_SET (dest, gen_rtx_NEG (mode, clobber_vlenb)));
            emit_insn (
                    gen_rtx_SET (dest, gen_rtx_ASHIFT (mode, dest, GEN_INT (log2))));
        }
        else
            emit_insn (gen_rtx_SET (dest, gen_rtx_ASHIFT (mode, clobber_vlenb,
                                                          GEN_INT (log2))));
    }
    else if (exact_log2 (quotient + 1) != -1
             && GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode))
    {
        gcc_assert (IN_RANGE (exact_log2 (quotient + 1), 0, 31));
        emit_insn (
                gen_rtx_SET (dest,
                             gen_rtx_ASHIFT (mode, clobber_vlenb,
                                             GEN_INT (exact_log2 (quotient + 1)))));

        if (is_neg)
            emit_insn (
                    gen_rtx_SET (dest, gen_rtx_MINUS (mode, clobber_vlenb, dest)));
        else
            emit_insn (
                    gen_rtx_SET (dest, gen_rtx_MINUS (mode, dest, clobber_vlenb)));
    }
    else if (exact_log2 (quotient - 1) != -1
             && GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode))
    {
        gcc_assert (IN_RANGE (exact_log2 (quotient - 1), 0, 31));
        emit_insn (
                gen_rtx_SET (dest,
                             gen_rtx_ASHIFT (mode, clobber_vlenb,
                                             GEN_INT (exact_log2 (quotient - 1)))));

        if (is_neg)
        {
            emit_insn (gen_rtx_SET (dest, gen_rtx_NEG (mode, dest)));
            emit_insn (
                    gen_rtx_SET (dest, gen_rtx_MINUS (mode, dest, clobber_vlenb)));
        }
        else
            emit_insn (
                    gen_rtx_SET (dest, gen_rtx_PLUS (mode, dest, clobber_vlenb)));
    }
    else
    {
        gcc_assert (TARGET_MUL
                    && "M-extension must be enabled to calculate the poly_int "
                       "size/offset.");

        if (is_neg)
            riscv_emit_move (dest, GEN_INT (-quotient));
        else
            riscv_emit_move (dest, GEN_INT (quotient));

        if (GET_MODE_SIZE (mode).to_constant () <= GET_MODE_SIZE (Pmode))
            emit_insn (
                    gen_rtx_SET (dest, gen_rtx_MULT (mode, dest, clobber_vlenb)));
        else
        {
            /* We should use SImode to simulate DImode multiplication. */
            /* prologue and epilogue can not go through this condition. */
            gcc_assert (can_create_pseudo_p ());
            rtx reg = gen_reg_rtx (Pmode);
            emit_insn (gen_umulsi3_highpart (reg, gen_lowpart (Pmode, dest),
                                             gen_lowpart (Pmode, clobber_vlenb)));
            emit_insn (
                    gen_rtx_SET (gen_highpart (Pmode, clobber_vlenb),
                                 gen_rtx_MULT (Pmode,
                                               gen_highpart (Pmode, clobber_vlenb),
                                               gen_lowpart (Pmode, dest))));
            emit_insn (
                    gen_rtx_SET (gen_highpart (Pmode, dest),
                                 gen_rtx_MULT (Pmode, gen_highpart (Pmode, dest),
                                               gen_lowpart (Pmode, clobber_vlenb))));
            emit_insn (
                    gen_rtx_SET (gen_lowpart (Pmode, dest),
                                 gen_rtx_MULT (Pmode, gen_lowpart (Pmode, dest),
                                               gen_lowpart (Pmode, clobber_vlenb))));
            emit_insn (
                    gen_rtx_SET (gen_highpart (Pmode, dest),
                                 gen_rtx_PLUS (Pmode, gen_highpart (Pmode, dest),
                                               gen_highpart (Pmode, clobber_vlenb))));
            emit_insn (
                    gen_rtx_SET (gen_highpart (Pmode, dest),
                                 gen_rtx_PLUS (Pmode, gen_highpart (Pmode, dest),
                                               reg)));
        }
    }
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

void riscv_vector_adjust_frame (rtx target, poly_int64 offset, bool epilogue)
{
    rtx clobber = RISCV_PROLOGUE_TEMP (Pmode);
    rtx space = RISCV_PROLOGUE_TEMP2 (Pmode);
    rtx insn, dwarf, adjust_frame_rtx;

    riscv_vector_expand_poly_move (Pmode, space, clobber,
                                   gen_int_mode (offset, Pmode));

    if (epilogue)
    {
        insn = gen_add3_insn (target, target, space);
    }
    else
    {
        insn = gen_sub3_insn (target, target, space);
    }

    insn = emit_insn (insn);

    RTX_FRAME_RELATED_P (insn) = 1;

    adjust_frame_rtx
            = gen_rtx_SET (target,
                           plus_constant (Pmode, target, epilogue ? offset : -offset));

    dwarf = alloc_reg_note (REG_FRAME_RELATED_EXPR, copy_rtx (adjust_frame_rtx),
                            NULL_RTX);

    REG_NOTES (insn) = dwarf;
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