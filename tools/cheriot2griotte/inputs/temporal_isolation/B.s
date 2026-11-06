	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"B.cc"
	.section	.text._Z1fPVi,"ax",@progbits
	.globl	_Z1fPVi                         # -- Begin function _Z1fPVi
	.p2align	1
	.type	_Z1fPVi,@function
_Z1fPVi:                                # @_Z1fPVi
# %bb.0:
	ct.cincoffset	sp, sp, -16
	li	a1, 7
	ct.csw	a1, 0(a0)
.LBB0_1:                                # Label of block must be emitted
	ct.auicgp	a1, %cheriot_compartment_hi(stash)
	ct.cincoffset	a1, a1, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csc	a0, 0(a1)
	ct.csc	a0, 8(sp)
	#APP
	ecall
	#NO_APP
	li	a0, 0
	li	a1, 0
	ct.cincoffset	sp, sp, 16
	ct.cret
.Lfunc_end0:
	.size	_Z1fPVi, .Lfunc_end0-_Z1fPVi
                                        # -- End function
	.section	.text._Z3advv,"ax",@progbits
	.globl	_Z3advv                         # -- Begin function _Z3advv
	.p2align	1
	.type	_Z3advv,@function
_Z3advv:                                # @_Z3advv
# %bb.0:
	li	a0, 3
.LBB1_5:                                # Label of block must be emitted
	ct.auicgp	a1, %cheriot_compartment_hi(stash)
	ct.cincoffset	a1, a1, %cheriot_compartment_lo_i(.LBB1_5)
	li	a2, 13
	beqz	a0, .LBB1_4
.LBB1_1:                                # =>This Inner Loop Header: Depth=1
	ct.clc	a3, 0(a1)
	ct.cgettag	a4, a3
	beqz	a4, .LBB1_3
# %bb.2:                                #   in Loop: Header=BB1_1 Depth=1
	ct.csw	a2, 0(a3)
.LBB1_3:                                #   in Loop: Header=BB1_1 Depth=1
	#APP
	ecall
	#NO_APP
	addi	a0, a0, -1
	bnez	a0, .LBB1_1
.LBB1_4:
	li	a1, 0
	ct.cret
.Lfunc_end1:
	.size	_Z3advv, .Lfunc_end1-_Z3advv
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

	.type	stash,@object                   # @stash
	.section	.bss.stash,"aw",@nobits
	.globl	stash
	.p2align	3, 0x0
stash:
	.chericap	0
	.size	stash, 8

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym stash
	.section	.compartment_exports,"aR",@progbits
	.type	__export_B__Z1fPVi,@object
	.globl	__export_B__Z1fPVi
	.p2align	2, 0x0
__export_B__Z1fPVi:
	.half	_Z1fPVi-__compartment_pcc_start
	.byte	2
	.byte	9
	.size	__export_B__Z1fPVi, 4
	.type	__export_B__Z3advv,@object
	.globl	__export_B__Z3advv
	.p2align	2, 0x0
__export_B__Z3advv:
	.half	_Z3advv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_B__Z3advv, 4
