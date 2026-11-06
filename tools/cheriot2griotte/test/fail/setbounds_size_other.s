# Rejection test of the lowering: csetbounds to the size of a global the source does not point to (D34)
	.section	.text._Z3runv,"ax",@progbits
	.globl	_Z3runv
_Z3runv:
.LBB0_1:
	ct.auicgp	a0, %cheriot_compartment_hi(b)
	ct.cincoffset	a0, a0, %cheriot_compartment_lo_i(.LBB0_1)
	ct.csetbounds	a0, a0, %cheriot_compartment_size(c)
	ct.cret
.Lfunc_end0:
	.size	_Z3runv, .Lfunc_end0-_Z3runv
	.section	.bss.b,"aw",@nobits
	.globl	b
b:
	.word	0
	.size	b, 4
	.section	.bss.c,"aw",@nobits
	.globl	c
c:
	.word	0
	.size	c, 4

	.section	.compartment_exports,"aR",@progbits
	.globl	__export_main__Z3runv
__export_main__Z3runv:
	.half	_Z3runv-__compartment_pcc_start
	.byte	0
	.byte	8
	.size	__export_main__Z3runv, 4
