# Rejection test of the lowering: a capability global other than a single null capability (D6)
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv
	.section	.data.a,"aw",@progbits
	.globl	a
a:
	.chericap	b
	.size	a, 8
	.section	.compartment_exports,"aR",@progbits
	.globl	__export_main__Z3runv
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_main__Z3runv, 4
