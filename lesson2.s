	.org $8000

reset:
	ldx #0
loop:
	lda hello,x
	cmp #0
	beq done
	sta $7000
	inx
	jmp loop
done:
	stp	
	

hello: .asciiz "Hello world"
	
	.org $fffc
	.word reset




