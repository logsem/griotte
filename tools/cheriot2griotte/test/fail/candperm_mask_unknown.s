# Rejection test of the lowering: candperm with a mask not known to be a constant
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
.LBB0_1:
	ct.auicgp	a0, %cheriot_compartment_hi(b)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.candperm	a0, a0, a1
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv
	.section	.bss.b,"aw",@nobits
	.globl	b
b:
	.word	0
	.size	b, 4
	.section	.compartment_exports,"aR",@progbits
	.globl	__export_main__Z3runv
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_main__Z3runv, 4
