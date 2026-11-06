# Rejection test of the lowering: a switcher call whose target in t1 is loaded, neither fetched from an import nor moved from a register
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
	ct.clc	t1, 0(a0)
.LBB0_2:
	ct.auipcc	t2, %cheriot_compartment_hi(.compartment_switcher)
	ct.clc	t2, %cheriot_compartment_lo_i(.LBB0_2)(t2)
	ct.cjalr	t2
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
