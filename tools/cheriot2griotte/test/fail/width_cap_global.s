# Rejection test of the lowering: integer store to a capability global (D34)
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
.LBB0_1:
	ct.auicgp	a0, %cheriot_compartment_hi(c)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csetbounds	a0, a0, %cheriot_compartment_size(c)
	ct.csw	zero, 0(a0)
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv
	.section	.data.c,"aw",@progbits
	.globl	c
c:
	.chericap	0
	.size	c, 8

	.section	.compartment_exports,"aR",@progbits
	.globl	__export_main__Z3runv
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_main__Z3runv, 4
