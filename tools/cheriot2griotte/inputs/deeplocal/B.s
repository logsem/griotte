	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"B.cc"
	.section	.text._Z1fPPi,"ax",@progbits
	.globl	_Z1fPPi                         # -- Begin function _Z1fPPi
	.p2align	1
	.type	_Z1fPPi,@function
_Z1fPPi:                                # @_Z1fPPi
# %bb.0:
	beqz	a0, .LBB0_2
# %bb.1:
	ct.clc	a1, 0(a0)
	li	a2, 7
	ct.csw	a2, 0(a1)
.LBB0_8:                                # Label of block must be emitted
	ct.auicgp	a2, %cheriot_compartment_hi(keptA)
	ct.cincoffset	a2, a2, %cheriot_compartment_lo_i(.LBB0_8)
	ct.csc	a0, 0(a2)
.LBB0_9:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(keptB)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_9)
	ct.csc	a1, 0(a0)
	j	.LBB0_7
.LBB0_2:
.LBB0_10:                               # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(keptB)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_10)
	ct.clc	a1, 0(a0)
	ct.cgettag	a1, a1
	beqz	a1, .LBB0_4
.LBB0_3:
	ct.clc	a0, 0(a0)
	li	a1, 13
	ct.csw	a1, 0(a0)
	j	.LBB0_7
.LBB0_4:
.LBB0_11:                               # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(keptA)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_11)
	ct.clc	a1, 0(a0)
	ct.cgettag	a1, a1
	beqz	a1, .LBB0_7
# %bb.5:
	ct.clc	a1, 0(a0)
	ct.clc	a1, 0(a1)
	ct.cgettag	a1, a1
	beqz	a1, .LBB0_7
# %bb.6:
	ct.clc	a0, 0(a0)
	j	.LBB0_3
.LBB0_7:
	li	a0, 0
	li	a1, 0
	ct.cret
.Lfunc_end0:
	.size	_Z1fPPi, .Lfunc_end0-_Z1fPPi
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

	.type	keptA,@object                   # @keptA
	.section	.bss.keptA,"aw",@nobits
	.globl	keptA
	.p2align	3, 0x0
keptA:
	.chericap	0
	.size	keptA, 8

	.type	keptB,@object                   # @keptB
	.section	.bss.keptB,"aw",@nobits
	.globl	keptB
	.p2align	3, 0x0
keptB:
	.chericap	0
	.size	keptB, 8

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.addrsig_sym __export.sealing_type.allocator.MallocKey
	.addrsig_sym __default_malloc_capability
	.addrsig_sym keptA
	.addrsig_sym keptB
	.section	.compartment_exports,"aR",@progbits
	.type	__export_B__Z1fPPi,@object
	.globl	__export_B__Z1fPPi
	.p2align	2, 0x0
__export_B__Z1fPPi:
	.half	_Z1fPPi-__compartment_pcc_start
	.byte	0
	.byte	9
	.size	__export_B__Z1fPPi, 4
