PORTB1 = $6000
PORTA1 = $6001
DDRB1 = $6002
DDRA1 = $6003
T1CL1 = $6004
T1CH1 = $6005
T1LL1 = $6006
T1LH1 = $6007
SR1 = $600a
ACR1 = $600b
PCR1 = $600c
IFR1 = $600d
IER1 = $600e

	.org $8000
reset:
	lda #%11000000 ;Enable Timer 1 VIA 1 interrupt.
	sta IER1

	;Setup Aux. 
	lda #%01000000
	sta ACR1 ;Contious interrupts, PB7 square wave diabled.

	;Init timer 1 on VIA 1
	lda #136 ;Low byte of 5000
	sta T1CL1 ;Load T1 low latches

	lda #19 ;High byte of 5000
	sta T1CH1 ;Loads T1 high latches and start countdown. Also reset Timer 1 IRQ flag.

loop:
	jmp loop


irq:
	pha
	phx
	phy
	php

	;VIA 1 Interrupts
	
	;Timer 1 interrupt
	lda IFR1
	and #%11000000
	cmp #%11000000
	beq t1_1_irq

	jmp irq_done


t1_1_irq:
	lda #"A"
	sta $6200
	jmp irq_done

;IRQ BRIDGES HERE
irq_done:
	plp
	ply
	plx
	pla
	rti


nmi:
	rti


	.org $fffa
	.word nmi
	.word reset
	.word irq

