# Rejection test of the lowering: a compartment export with the inherited interrupt posture (R26)
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
	li	a0, 0
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv

	.section	.compartment_exports,"aR",@progbits
	.globl	__export_main__Z3runv
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	0
	.byte	0
	.size	__export_main__Z3runv, 4
