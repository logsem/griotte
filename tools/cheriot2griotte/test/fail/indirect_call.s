# Rejection test of the lowering: a call through a register not fetched from an import
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
	ct.cjalr	a0
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv

	.section	.compartment_exports,"aR",@progbits
	.globl	__export_main__Z3runv
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_main__Z3runv, 4
