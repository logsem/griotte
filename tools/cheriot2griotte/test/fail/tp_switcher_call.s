# Rejection test of the lowering: the switcher zeroes tp on return, so tp is unknown after a cross-compartment call (D34)
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
	li	tp, 1
.LBB0_1:
	ct.auipcc	t1, %cheriot_compartment_hi(__import_B__Z1fv)
	ct.clc	t1, %cheriot_compartment_lo_i(.LBB0_1)(t1)
.LBB0_2:
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_2)(t2)
	ct.cjalr	t2
	li	a1, 2
	bltu	tp, a1, .LBB0_3
.LBB0_3:
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
	.section	.compartment_imports._Z1fv,"aG",@progbits,__import_B__Z1fv,comdat
	.weak	__import_B__Z1fv
__import_B__Z1fv:
	.word	__export_B__Z1fv
	.word	0
	.size	__import_B__Z1fv, 8
