	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"griotte_locks.cc"
	.section	.text._Z8try_lockPi,"ax",@progbits
	.globl	_Z8try_lockPi                   # -- Begin function _Z8try_lockPi
	.p2align	1
	.type	_Z8try_lockPi,@function
_Z8try_lockPi:                          # @_Z8try_lockPi
# %bb.0:
	ct.cmove	a1, a0
	ct.clw	a0, 0(a0)
	beqz	a0, .LBB0_2
# %bb.1:
	li	a0, -1
	ct.cret
.LBB0_2:
	li	a2, 1
	ct.csw	a2, 0(a1)
	ct.cret
.Lfunc_end0:
	.size	_Z8try_lockPi, .Lfunc_end0-_Z8try_lockPi
                                        # -- End function
	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.section	.compartment_exports,"aR",@progbits
	.type	__library_export_libcalls__Z8try_lockPi,@object
	.globl	__library_export_libcalls__Z8try_lockPi
	.p2align	2, 0x0
__library_export_libcalls__Z8try_lockPi:
	.half	_Z8try_lockPi-__compartment_pcc_start
	.byte	0
	.byte	17
	.size	__library_export_libcalls__Z8try_lockPi, 4
