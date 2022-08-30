	.org $8000

reset:
	lda $6200
	beq reset
	sta $6200
	bra reset

	.org $fffc
	.word reset
	











