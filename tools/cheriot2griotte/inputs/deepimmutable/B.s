	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"B.cc"
                                        # Start of file scope inline assembly
	.section	.text.setjmp,"axwG",@progbits,setjmp,comdat
	.globl	setjmp
	.p2align	2
	.type	setjmp,@function
setjmp:
	ct.csc	s0, 0(a0)
	ct.csc	s1, 8(a0)
	ct.csc	sp, 16(a0)
	ct.csc	ra, 24(a0)
	li	a0, 0
	ct.cret
	.section	.text.longjmp,"axwG",@progbits,longjmp,comdat
	.globl	longjmp
	.p2align	2
	.type	longjmp,@function
longjmp:
	ct.clc	s0, 0(a0)
	ct.clc	s1, 8(a0)
	ct.clc	sp, 16(a0)
	ct.clc	ra, 24(a0)
	mv	a0, a1
	ct.cret

                                        # End of file scope inline assembly
	.section	.text._Z1fPPi,"ax",@progbits
	.globl	_Z1fPPi                         # -- Begin function _Z1fPPi
	.p2align	1
	.type	_Z1fPPi,@function
_Z1fPPi:                                # @_Z1fPPi
# %bb.0:
	ct.cincoffset	sp, sp, -16
	ct.csc	ra, 8(sp)                       # 8-byte Folded Spill
	ct.csc	s0, 0(sp)                       # 8-byte Folded Spill
	ct.cmove	s0, a0
	ct.ccall	_ZL11try_write_bPPi
	ct.cmove	a0, s0
	ct.clc	ra, 8(sp)                       # 8-byte Folded Reload
	ct.clc	s0, 0(sp)                       # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 16
	ct.ctail	_ZL11try_write_aPPi
.Lfunc_end0:
	.size	_Z1fPPi, .Lfunc_end0-_Z1fPPi
                                        # -- End function
	.section	.text._ZL11try_write_bPPi,"ax",@progbits
	.p2align	1                               # -- Begin function _ZL11try_write_bPPi
	.type	_ZL11try_write_bPPi,@function
_ZL11try_write_bPPi:                    # @_ZL11try_write_bPPi
# %bb.0:
	ct.cincoffset	sp, sp, -64
	ct.csc	ra, 56(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 48(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 40(sp)                      # 8-byte Folded Spill
	ct.cmove	a1, sp
	ct.cgettop	a2, a1
	addi	a2, a2, -8
	ct.csetaddr	a1, a1, a2
	ct.csetbounds	s0, a1, 8
	ct.clc	a1, 0(s0)
	ct.clc	s1, 0(a0)
	ct.csc	a1, 0(sp)
	ct.cincoffset	a0, sp, 0
	ct.csetbounds	a0, a0, 40
	ct.csc	a0, 0(s0)
	ct.cincoffset	a0, a0, 8
	ct.ccall	setjmp
	bnez	a0, .LBB1_2
# %bb.1:
	li	a0, 37
	ct.csw	a0, 0(s1)
.LBB1_2:
	ct.clc	a0, 0(sp)
	ct.csc	a0, 0(s0)
	ct.clc	ra, 56(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 48(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 40(sp)                      # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 64
	ct.cret
.Lfunc_end1:
	.size	_ZL11try_write_bPPi, .Lfunc_end1-_ZL11try_write_bPPi
                                        # -- End function
	.section	.text._ZL11try_write_aPPi,"ax",@progbits
	.p2align	1                               # -- Begin function _ZL11try_write_aPPi
	.type	_ZL11try_write_aPPi,@function
_ZL11try_write_aPPi:                    # @_ZL11try_write_aPPi
# %bb.0:
	ct.cincoffset	sp, sp, -64
	ct.csc	ra, 56(sp)                      # 8-byte Folded Spill
	ct.csc	s0, 48(sp)                      # 8-byte Folded Spill
	ct.csc	s1, 40(sp)                      # 8-byte Folded Spill
	ct.cmove	s0, a0
	ct.cmove	a0, sp
	ct.cgettop	a1, a0
	addi	a1, a1, -8
	ct.csetaddr	a0, a0, a1
	ct.csetbounds	s1, a0, 8
	ct.clc	a0, 0(s1)
	ct.csc	a0, 0(sp)
	ct.cincoffset	a0, sp, 0
	ct.csetbounds	a0, a0, 40
	ct.csc	a0, 0(s1)
	ct.cincoffset	a0, a0, 8
	ct.ccall	setjmp
	bnez	a0, .LBB2_2
# %bb.1:
.LBB2_3:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(c)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB2_3)
	ct.csc	a0, 0(s0)
.LBB2_2:
	ct.clc	a0, 0(sp)
	ct.csc	a0, 0(s1)
	ct.clc	ra, 56(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 48(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 40(sp)                      # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 64
	ct.cret
.Lfunc_end2:
	.size	_ZL11try_write_aPPi, .Lfunc_end2-_ZL11try_write_aPPi
                                        # -- End function
	.type	__default_malloc_capability,@object # @__default_malloc_capability
	.section	.sealed_objects,"awG",@progbits,__default_malloc_capability,comdat
	.weak	__default_malloc_capability
	.p2align	3, 0x0
__default_malloc_capability:
	.word	__export.sealing_type.allocator.MallocKey
	.word	0                               # 0x0
	.word	4096                            # 0x1000
	.word	0                               # 0x0
	.zero	16
	.size	__default_malloc_capability, 32

	.type	c,@object                       # @c
	.section	.bss.c,"aw",@nobits
	.globl	c
	.p2align	2, 0x0
c:
	.word	0                               # 0x0
	.size	c, 4

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym c
	.section	.compartment_exports,"aR",@progbits
	.type	__export_B__Z1fPPi,@object
	.globl	__export_B__Z1fPPi
	.p2align	2, 0x0
__export_B__Z1fPPi:
	.half	_Z1fPPi-__compartment_pcc_start
	.byte	2
	.byte	9
	.size	__export_B__Z1fPPi, 4
