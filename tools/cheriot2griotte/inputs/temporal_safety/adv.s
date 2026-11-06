	.attribute	4, 16
	.attribute	5, "rv32e2p0_m2p0_c2p0_zmmul1p0_zca1p0_xcheri0p0_xcheriot1p0_xcheripurecap0p0"
	.file	"adv.cc"
	.section	.text._Z3advPPi,"ax",@progbits
	.globl	_Z3advPPi                       # -- Begin function _Z3advPPi
	.p2align	1
	.type	_Z3advPPi,@function
_Z3advPPi:                              # @_Z3advPPi
# %bb.0:
.LBB0_6:                                # Label of block must be emitted
	ct.auicgp	a1, %cheriot_compartment_hi(cnt)
	ct.cincoffset	a1, a1, %cheriot_compartment_lo_i(.LBB0_6)
	ct.clw	a2, 0(a1)
	beqz	a2, .LBB0_2
# %bb.1:
.LBB0_7:                                # Label of block must be emitted
	ct.auicgp	a0, %cheriot_compartment_hi(copy_buf)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_7)
	ct.clc	a0, 0(a0)
	j	.LBB0_3
.LBB0_2:
	ct.clc	a2, 0(a0)
	li	a3, 999
	ct.csw	a3, 0(a2)
	ct.clw	a2, 0(a1)
.LBB0_8:                                # Label of block must be emitted
	ct.auicgp	a3, %cheriot_compartment_hi(copy_buf)
	ct.cincoffset	a3, a3, %cheriot_compartment_lo_i(.LBB0_8)
	ct.csc	a0, 0(a3)
	beqz	a2, .LBB0_5
.LBB0_3:
	ct.clc	a0, 0(a0)
	li	a2, 666
	ct.csw	a2, 0(a0)
	ct.clw	a0, 0(a1)
	addi	a0, a0, 1
.LBB0_4:
	ct.csw	a0, 0(a1)
	li	a0, 0
	li	a1, 0
	ct.cret
.LBB0_5:
	li	a0, 1
	j	.LBB0_4
.Lfunc_end0:
	.size	_Z3advPPi, .Lfunc_end0-_Z3advPPi
                                        # -- End function
	.type	copy_buf,@object                # @copy_buf
	.section	.bss.copy_buf,"aw",@nobits
	.globl	copy_buf
	.p2align	3, 0x0
copy_buf:
	.chericap	0
	.size	copy_buf, 8

	.type	cnt,@object                     # @cnt
	.section	.bss.cnt,"aw",@nobits
	.globl	cnt
	.p2align	2, 0x0
cnt:
	.word	0                               # 0x0
	.size	cnt, 4

	.ident	"clang version 21.1.7 (CHERIoT-Platform/llvm-project-DLLVM_VC_REVISION=2b6c51c910ebe464ae686520aa2ba253b9e5f19e)"
	.section	".note.GNU-stack","",@progbits
	.addrsig
	.section	.compartment_exports,"aR",@progbits
	.type	__export_adv__Z3advPPi,@object
	.globl	__export_adv__Z3advPPi
	.p2align	2, 0x0
__export_adv__Z3advPPi:
	.half	_Z3advPPi-__compartment_pcc_start
	.byte	0
	.byte	9
	.size	__export_adv__Z3advPPi, 4
