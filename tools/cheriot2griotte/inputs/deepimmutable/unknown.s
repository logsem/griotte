	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"unknown.cc"
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
	.section	.text._Z3advPPi,"ax",@progbits
	.globl	_Z3advPPi                       # -- Begin function _Z3advPPi
	.p2align	1
	.type	_Z3advPPi,@function
_Z3advPPi:                              # @_Z3advPPi
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
	bnez	a0, .LBB0_2
# %bb.1:
	li	a0, 37
	ct.csw	a0, 0(s1)
.LBB0_2:
	li	a0, 0
	ct.clc	a1, 0(sp)
	ct.csc	a1, 0(s0)
	li	a1, 0
	ct.clc	ra, 56(sp)                      # 8-byte Folded Reload
	ct.clc	s0, 48(sp)                      # 8-byte Folded Reload
	ct.clc	s1, 40(sp)                      # 8-byte Folded Reload
	ct.cincoffset	sp, sp, 64
	ct.cret
.Lfunc_end0:
	.size	_Z3advPPi, .Lfunc_end0-_Z3advPPi
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

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.section	.compartment_exports,"aR",@progbits
	.type	__export_unknown__Z3advPPi,@object
	.globl	__export_unknown__Z3advPPi
	.p2align	2, 0x0
__export_unknown__Z3advPPi:
	.half	_Z3advPPi-__compartment_pcc_start
	.byte	8
	.byte	9
	.size	__export_unknown__Z3advPPi, 4
