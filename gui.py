# -*- coding: utf-8 -*-
"""
Created on Sun Mar 13 17:19:56 2022

@author: Eric Buehler
"""

from tkinter.filedialog import askopenfile
from tkinter import ttk,scrolledtext

from tkinter import * 

import tkinter as tk
import tkinter

from collections import defaultdict
from tkinter.filedialog import asksaveasfile
from threading import *

import subprocess
import shlex
from tkinter import simpledialog
import os

import random
import re

import tqdm

import time


def itoa(num, base=10):
    """Convert a decimal number to its equivalent in base 2 or 16; base 10
    is silently passed through. Other bases raise a ValueError. Returns a
    string with hex digits lowercase.
    """
    fmt = _itoa_fmts.get(base)
    if fmt is None:
        messagebox.showerror("ValueError","Unsupported base: %r" % base)
        return
    return fmt.format(num)

def make_instruction_decorator(instruct, disasm, allcycles, allextras):
    def instruction(name, mode, cycles, extracycles=0):
        def decorate(f):
            opcode = int(f.__name__.split('_')[-1], 16)
            instruct[opcode] = f
            disasm[opcode] = (name, mode)
            allcycles[opcode] = cycles
            allextras[opcode] = extracycles
            return f  # Return the original function
        return decorate
    return instruction




class ObservableMemory:
    def __init__(self, subject=None, addrWidth=16):
        self.physMask = 0xffff
        if addrWidth > 16:
            # even with 32-bit address space, model only 256k memory
            self.physMask = 0x3ffff

        if subject is None:
            subject = (self.physMask + 1) * [0x00]
        self._subject = subject

        self._read_subscribers = defaultdict(list)
        self._write_subscribers = defaultdict(list)
        
    def __len__(self):
        return len(self._subject)

    def __setitem__(self, address, value):
        if isinstance(address, slice):
            r = range(*address.indices(self.physMask + 1))
            for n, v in zip(r, value):
                self[n] = v
            return

        address &= self.physMask
        callbacks = self._write_subscribers[address]

        for callback in callbacks:
            result = callback(address, value)
            if result is not None:
                value = result

                self._subject[address] = value

    def __getitem__(self, address):
        if isinstance(address, slice):
            r = range(*address.indices(self.physMask + 1))
            return [ self[n] for n in r ]

        address &= self.physMask
        callbacks = self._read_subscribers[address]
        final_result = None

        for callback in callbacks:
           
            result = callback(address)
            if result is not None:
                final_result = result

        if final_result is None:
            return random.randint(0,255)
        else:
            return final_result

    def __getattr__(self, attribute):
        return getattr(self._subject, attribute)

    def subscribe_to_write(self, address_range, callback):
        for address in address_range:
            address &= self.physMask
            callbacks = self._write_subscribers.setdefault(address, [])
            if callback not in callbacks:
                callbacks.append(callback)

    def subscribe_to_read(self, address_range, callback):
        for address in address_range:
            address &= self.physMask
            callbacks = self._read_subscribers.setdefault(address, [])
            if callback not in callbacks:
                callbacks.append(callback)

    def write(self, start_address, bytes):
        start_address &= self.physMask
        self._subject[start_address:start_address + len(bytes)] = bytes
        

class AddressParser(object):
    """Parse user input into addresses or ranges of addresses.
    """

    def __init__(self, maxwidth=16, radix=16, labels={}):
        """Maxwidth is the maximum width of an address in bits.
        Radix is the default radix to use when one is not specified
        as a prefix of any input.  Labels are a dictionary of label
        names that can be substituted for addresses.
        """
        self.radix = radix
        self.maxwidth = maxwidth

        self.labels = {}
        for k, v in labels.items():
            self.labels[k] = self._constrain(v)

    def _get_maxwidth(self):
        return self._maxwidth

    def _set_maxwidth(self, width):
        self._maxwidth = width
        self._maxaddr = pow(2, width) - 1

    maxwidth = property(_get_maxwidth, _set_maxwidth)

    def address_for(self, label, default=None):
        """Given a label, return the corresponding address or a default.
        """
        return self.labels.get(label, default)

    def label_for(self, address, default=None):
        """Given an address, return the corresponding label or a default.
        """
        for label, label_address in self.labels.items():
            if label_address == address:
                return label
        return default

    def number(self, num):
        """Parse a string containing a label or number into an address.
        """
        try:
            if num[0:2] == "#$":
                # hexadecimal
                return self._constrain(int(num[2:], 16))

            if num.startswith('$'):
                # hexadecimal
                return self._constrain(int(num[1:], 16))

            elif num.startswith('#'):
                # decimal
                return self._constrain(int(num[1:], 10))

            elif num.startswith('%'):
                # binary
                return self._constrain(int(num[1:], 2))

            elif num in self.labels:
                # label name
                return self.labels[num]

            else:
                matches = re.match('^([^\s+-]+)\s*([+\-])\s*([$+%]?\d+)$', num)
                if matches:
                    label, sign, offset = matches.groups()

                    if label not in self.labels:
                        raise KeyError("Label not found: %s" % label)

                    base = self.labels[label]
                    offset = self.number(offset)

                    if sign == '+':
                        address = base + offset
                    else:
                        address = base - offset

                    return self._constrain(address)

                else:
                    return self._constrain(int(num, self.radix))

        except ValueError:
            raise KeyError("Label not found: %s" % num)

    def range(self, addresses):
        """Parse a string containing an address or a range of addresses
        into a tuple of (start address, end address)
        """
        matches = re.match('^([^:,]+)\s*[:,]+\s*([^:,]+)$', addresses)
        if matches:
            start, end = map(self.number, matches.groups(0))
        else:
            start = end = self.number(addresses)

        if start > end:
            start, end = end, start
        return (start, end)

    def _constrain(self, address):
        '''Raises OverflowError if the address is illegal'''
        if address < 0 or address > self._maxaddr:
            raise OverflowError(address)
        return address


class Assembler:
    Statement = re.compile(r'^([A-z]{3}[0-7]?\s+'
                           r'\(?\s*)([^,\s\)]+)(\s*[,xXyY\s]*\)?'
                           r'[,xXyY\s]*)$')

    Addressing = (
        ('zpi', "($00FF)"),
        ('zpx', "$00FF,X"),
        ('zpy', "$00FF,Y"),
        ('zpg', "$00FF"),
        ('inx', "($00FF,X)"),
        ('iax', "($FFFF,X)"),
        ('iny', "($00FF),Y"),
        ('ind', "($FFFF)"),
        ('abx', "$FFFF,X"),
        ('aby', "$FFFF,Y"),
        ('abs', "$FFFF"),
        ('rel', "$FFFF"),
        ('imp', ""),
        ('acc', ""),
        ('acc', "A"),
        ('imm', "#$FF")
    )

    def __init__(self, mpu, address_parser=None):
        """ If a configured AddressParser is passed, symbolic addresses
        may be used in the assembly statements.
        """
        self._mpu = mpu

        if address_parser is None:
            address_parser = AddressParser()
        self._address_parser = address_parser

        self._addressing = []
        numchars = mpu.BYTE_WIDTH / 4  # 1 byte = 2 chars in hex
        for mode, format in self.Addressing:
            pat = "^" + re.escape(format) + "$"
            pat = pat.replace('00', '0{%d}' % numchars)
            pat = pat.replace('FF', '([0-9A-F]{%d})' % numchars)
            self._addressing.append([mode, re.compile(pat)])
    
    def getlabels(self):
        return self._address_parser.labels

    def assemble(self, statement, pc=0000):
        """ Assemble the given assembly language statement.  If the statement
        uses relative addressing, the program counter (pc) must also be given.
        The result is a list of bytes.  Raises when assembly fails.
        """
        opcode, operand = self.normalize_and_split(statement)
        #print(operand)

        for mode, pattern in self._addressing:
            match = pattern.match(operand)
            #print(mode,match)

            if match:
                # check if opcode supports this addressing mode
                try:
                    bytes = [self._mpu.disassemble.index((opcode, mode))]
                except ValueError:
                    continue

                operands = match.groups()

                if mode == 'rel':
                    # relative branch
                    absolute = int(''.join(operands), 16)
                    relative = (absolute - pc) - 2
                    relative = relative & self._mpu.byteMask
                    operands = [(self._mpu.BYTE_FORMAT % relative)]

                elif len(operands) == 2:
                    # swap bytes
                    operands = (operands[1], operands[0])

                operands = [int(hex, 16) for hex in operands]
                bytes.extend(operands)

                # raise if the assembled bytes would exceed top of memory
                if (pc + len(bytes)) > (2 ** self._mpu.ADDR_WIDTH):
                    raise OverflowError

                return bytes

        # assembly failed
        if statement[-1]==":":
            self._address_parser.labels[statement[0:len(statement)-1]]=pc
            return None
        else: 
            raise SyntaxError(statement)

    def normalize_and_split(self, statement):
        """ Given an assembly language statement like "lda $c12,x", normalize
            the statement by uppercasing it, removing unnecessary whitespace,
            and parsing the address part using AddressParser.  The result of
            the normalization is a tuple of two strings (opcode, operand).
        """
        statement = ' '.join(str.split(statement))

        # normalize target in operand
        match = self.Statement.match(statement)
        if match:
            before, target, after = match.groups()
            
            # target is an immediate value
            if not target.startswith('#$') and target.startswith('#'):
                try:
                    if target[1] in ("'", '"'): # quoted ascii character
                        number = ord(target[2])
                    else:
                        number = self._address_parser.number(target)
                except IndexError:
                    raise SyntaxError(statement)

                if (number < 0) or (number > self._mpu.byteMask):
                    raise OverflowError
                #prisnt(before,number)
                statement = before + '#$' + self._mpu.BYTE_FORMAT % number
                #print(statement)
            # target is the accumulator
            elif target in ('a', 'A'):
                pass

            # target is an address or label
            else:
                address = self._address_parser.number(target)
                statement = before + '$' + self._mpu.ADDR_FORMAT % address + after

        # separate opcode and operand
        splitted = statement.split(" ", 2)
        opcode = splitted[0].strip().upper()
        if len(splitted) > 1:
            operand = splitted[1].strip().upper()
        else:
            operand = ''
        return (opcode, operand)
    
class Disassembler:
    def __init__(self, mpu, address_parser=None):
        if address_parser is None:
            address_parser = AddressParser()

        self._mpu = mpu
        self._address_parser = address_parser

        self.addrWidth = mpu.ADDR_WIDTH
        self.byteWidth = mpu.BYTE_WIDTH
        self.addrFmt = mpu.ADDR_FORMAT
        self.byteFmt = mpu.BYTE_FORMAT
        self.addrMask = mpu.addrMask
        self.byteMask = mpu.byteMask

    def instruction_at(self, pc):
        """ Disassemble the instruction at PC and return a tuple
        containing (instruction byte count, human readable text)
        """

        instruction = self._mpu.ByteAt(pc)
        disasm, addressing = self._mpu.disassemble[instruction]

        if addressing == 'acc':
            disasm += ' A'
            length = 1

        elif addressing == 'abs':
            address = self._mpu.WordAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                address, '$' + self.addrFmt % address)
            disasm += ' ' + address_or_label
            length = 3

        elif addressing == 'abx':
            address = self._mpu.WordAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                address, '$' + self.addrFmt % address)
            disasm += ' %s,X' % address_or_label
            length = 3

        elif addressing == 'aby':
            address = self._mpu.WordAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                address, '$' + self.addrFmt % address)
            disasm += ' %s,Y' % address_or_label
            length = 3

        elif addressing == 'imm':
            byte = self._mpu.ByteAt(pc + 1)
            disasm += ' #$' + self.byteFmt % byte
            length = 2

        elif addressing == 'imp':
            length = 1

        elif addressing == 'ind':
            address = self._mpu.WordAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                address, '$' + self.addrFmt % address)
            disasm += ' (%s)' % address_or_label
            length = 3

        elif addressing == 'iny':
            zp_address = self._mpu.ByteAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                zp_address, '$' + self.byteFmt % zp_address)
            disasm += ' (%s),Y' % address_or_label
            length = 2

        elif addressing == 'inx':
            zp_address = self._mpu.ByteAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                zp_address, '$' + self.byteFmt % zp_address)
            disasm += ' (%s,X)' % address_or_label
            length = 2

        elif addressing == 'iax':
            address = self._mpu.WordAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                address, '$' + self.addrFmt % address)
            disasm += ' (%s,X)' % address_or_label
            length = 3

        elif addressing == 'rel':
            opv = self._mpu.ByteAt(pc + 1)
            targ = pc + 2
            if opv & (1 << (self.byteWidth - 1)):
                targ -= (opv ^ self.byteMask) + 1
            else:
                targ += opv
            targ &= self.addrMask

            address_or_label = self._address_parser.label_for(
                targ, '$' + self.addrFmt % targ)
            disasm += ' ' + address_or_label
            length = 2

        elif addressing == 'zpi':
            zp_address = self._mpu.ByteAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                zp_address, '($' + self.byteFmt % zp_address + ')')
            disasm += ' %s' % address_or_label
            length = 2

        elif addressing == 'zpg':
            zp_address = self._mpu.ByteAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                zp_address, '$' + self.byteFmt % zp_address)
            disasm += ' %s' % address_or_label
            length = 2

        elif addressing == 'zpx':
            zp_address = self._mpu.ByteAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                zp_address, '$' + self.byteFmt % zp_address)
            disasm += ' %s,X' % address_or_label
            length = 2

        elif addressing == 'zpy':
            zp_address = self._mpu.ByteAt(pc + 1)
            address_or_label = self._address_parser.label_for(
                zp_address, '$' + self.byteFmt % zp_address)
            disasm += ' %s,Y' % address_or_label
            length = 2

        else:
            msg = "Addressing mode: %r" % addressing
            raise NotImplementedError(msg)

        return (length, disasm)


def convert_to_bin(bcd):
    return _bcd2bin[bcd]


def convert_to_bcd(bin):
    return _bin2bcd[bin]


_itoa_fmts = {
    2: "{0:b}",
    10: "{0}",
    16: "{0:x}"
}


_bcd2bin = (
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 10, 11, 12, 13,
    14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 30, 31, 32, 33, 34, 35, 36, 37,
    38, 39, 40, 41, 42, 43, 44, 45, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61,
    62, 63, 64, 65, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73,
    74, 75, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
    80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 90, 91,
    92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 100, 101,
    102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115,
    110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123,
    124, 125, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131,
    132, 133, 134, 135, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139,
    140, 141, 142, 143, 144, 145, 140, 141, 142, 143, 144, 145, 146, 147,
    148, 149, 150, 151, 152, 153, 154, 155, 150, 151, 152, 153, 154, 155,
    156, 157, 158, 159, 160, 161, 162, 163, 164, 165
)


_bin2bcd = (
    0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09,
    0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19,
    0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29,
    0x30, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39,
    0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47, 0x48, 0x49,
    0x50, 0x51, 0x52, 0x53, 0x54, 0x55, 0x56, 0x57, 0x58, 0x59,
    0x60, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69,
    0x70, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78, 0x79,
    0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89,
    0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99
)




class mpu6502_MPU:
    # vectors
    RESET = 0xfffc
    NMI = 0xfffa
    IRQ = 0xfffe

    # processor flags
    NEGATIVE = 128
    OVERFLOW = 64
    UNUSED = 32
    BREAK = 16
    DECIMAL = 8
    INTERRUPT = 4
    ZERO = 2
    CARRY = 1

    BYTE_WIDTH = 8
    BYTE_FORMAT = "%02x"
    ADDR_WIDTH = 16
    ADDR_FORMAT = "%04x"

    def __init__(self, memory=None, pc=0x0000):
        # config
        self.name = '6502'
        self.byteMask = ((1 << self.BYTE_WIDTH) - 1)
        self.addrMask = ((1 << self.ADDR_WIDTH) - 1)
        self.addrHighMask = (self.byteMask << self.BYTE_WIDTH)
        self.spBase = 1 << self.BYTE_WIDTH

        # vm status
        self.excycles = 0
        self.addcycles = False
        self.processorCycles = 0

        if memory is None:
            memory = 0x10000 * [0x00]
        self.memory = memory
        self.start_pc = pc

        # init
        self.reset()

    def reprformat(self):
        return ("%s       PC    AC XR  YR SP  NV-BDIZC\n"
                "%s: %04x  %02x  %02x  %02x  %02x  %s")#("%s PC  AC XR YR SP NV-BDIZC\n"
               # "%s: %04x %02x %02x %02x %02x %s")

    def __repr__(self):
        flags = itoa(self.p, 2).rjust(self.BYTE_WIDTH, '0')
        indent = ' ' * (len(self.name) + 2)

        return self.reprformat() % (indent, self.name, self.pc, self.a,
                                    self.x, self.y, self.sp, flags)

    def step(self):
        instructCode = self.memory[self.pc]
        self.pc = (self.pc + 1) & self.addrMask
        self.excycles = 0
        self.addcycles = self.extracycles[instructCode]
        self.instruct[instructCode](self)
        self.pc &= self.addrMask
        self.processorCycles += self.cycletime[instructCode] + self.excycles
        return self

    def reset(self):
        #Get reset address from memory
        #fffc/fffd lo/hi
        self.pc = self.WordAt(self.RESET)
        #print(self.pc)
        self.sp = self.byteMask
        self.a = 0
        self.x = 0
        self.y = 0
        self.p = self.BREAK | self.UNUSED
        self.processorCycles = 0

    def irq(self):
        # triggers a normal IRQ
        # this is very similar to the BRK instruction
        if self.p & self.INTERRUPT:
            return
        self.stPushWord(self.pc)
        self.p &= ~self.BREAK
        self.stPush(self.p | self.UNUSED)
        self.p |= self.INTERRUPT
        self.pc = self.WordAt(self.IRQ)
        self.processorCycles += 7
    
    def nmi(self):
        # triggers a NMI IRQ in the processor
        # this is very similar to the BRK instruction
        self.stPushWord(self.pc)
        self.p &= ~self.BREAK
        self.stPush(self.p | self.UNUSED)
        self.p |= self.INTERRUPT
        self.pc = self.WordAt(self.NMI)
        self.processorCycles += 7

    # Helpers for addressing modes

    def ByteAt(self, addr):
        return self.memory[addr]

    def WordAt(self, addr):
        return self.ByteAt(addr) + (self.ByteAt(addr + 1) << self.BYTE_WIDTH)

    def WrapAt(self, addr):
        wrap = lambda x: (x & self.addrHighMask) + ((x + 1) & self.byteMask)
        return self.ByteAt(addr) + (self.ByteAt(wrap(addr)) << self.BYTE_WIDTH)

    def ProgramCounter(self):
        return self.pc

    # Addressing modes

    def ImmediateByte(self):
        return self.ByteAt(self.pc)

    def ZeroPageAddr(self):
        return self.ByteAt(self.pc)

    def ZeroPageXAddr(self):
        return self.byteMask & (self.x + self.ByteAt(self.pc))

    def ZeroPageYAddr(self):
        return self.byteMask & (self.y + self.ByteAt(self.pc))

    def IndirectXAddr(self):
        return self.WrapAt(self.byteMask & (self.ByteAt(self.pc) + self.x))

    def IndirectYAddr(self):
        if self.addcycles:
            a1 = self.WrapAt(self.ByteAt(self.pc))
            a2 = (a1 + self.y) & self.addrMask
            if (a1 & self.addrHighMask) != (a2 & self.addrHighMask):
                self.excycles += 1
            return a2
        else:
            return (self.WrapAt(self.ByteAt(self.pc)) + self.y) & self.addrMask

    def AbsoluteAddr(self):
        return self.WordAt(self.pc)

    def AbsoluteXAddr(self):
        if self.addcycles:
            a1 = self.WordAt(self.pc)
            a2 = (a1 + self.x) & self.addrMask
            if (a1 & self.addrHighMask) != (a2 & self.addrHighMask):
                self.excycles += 1
            return a2
        else:
            return (self.WordAt(self.pc) + self.x) & self.addrMask

    def AbsoluteYAddr(self):
        if self.addcycles:
            a1 = self.WordAt(self.pc)
            a2 = (a1 + self.y) & self.addrMask
            if (a1 & self.addrHighMask) != (a2 & self.addrHighMask):
                self.excycles += 1
            return a2
        else:
            return (self.WordAt(self.pc) + self.y) & self.addrMask

    def BranchRelAddr(self):
        self.excycles += 1
        addr = self.ImmediateByte()
        self.pc += 1

        if addr & self.NEGATIVE:
            addr = self.pc - (addr ^ self.byteMask) - 1
        else:
            addr = self.pc + addr

        if (self.pc & self.addrHighMask) != (addr & self.addrHighMask):
            self.excycles += 1

        self.pc = addr & self.addrMask

    # stack

    def stPush(self, z):
        self.memory[self.sp + self.spBase] = z & self.byteMask
        self.sp -= 1
        self.sp &= self.byteMask

    def stPop(self):
        self.sp += 1
        self.sp &= self.byteMask
        return self.ByteAt(self.sp + self.spBase)

    def stPushWord(self, z):
        self.stPush((z >> self.BYTE_WIDTH) & self.byteMask)
        self.stPush(z & self.byteMask)

    def stPopWord(self):
        z = self.stPop()
        z += self.stPop() << self.BYTE_WIDTH
        return z

    def FlagsNZ(self, value):
        self.p &= ~(self.ZERO | self.NEGATIVE)
        if value == 0:
            self.p |= self.ZERO
        else:
            self.p |= value & self.NEGATIVE

    # operations

    def opORA(self, x):
        self.a |= self.ByteAt(x())
        self.FlagsNZ(self.a)

    def opASL(self, x):
        if x is None:
            tbyte = self.a
        else:
            addr = x()
            tbyte = self.ByteAt(addr)

        self.p &= ~(self.CARRY | self.NEGATIVE | self.ZERO)

        if tbyte & self.NEGATIVE:
            self.p |= self.CARRY
        tbyte = (tbyte << 1) & self.byteMask

        if tbyte:
            self.p |= tbyte & self.NEGATIVE
        else:
            self.p |= self.ZERO

        if x is None:
            self.a = tbyte
        else:
            self.memory[addr] = tbyte

    def opLSR(self, x):
        if x is None:
            tbyte = self.a
        else:
            addr = x()
            tbyte = self.ByteAt(addr)

        self.p &= ~(self.CARRY | self.NEGATIVE | self.ZERO)
        self.p |= tbyte & 1

        tbyte = tbyte >> 1
        if tbyte:
            pass
        else:
            self.p |= self.ZERO

        if x is None:
            self.a = tbyte
        else:
            self.memory[addr] = tbyte

    def opBCL(self, x):
        if self.p & x:
            self.pc += 1
        else:
            self.BranchRelAddr()

    def opBST(self, x):
        if self.p & x:
            self.BranchRelAddr()
        else:
            self.pc += 1

    def opCLR(self, x):
        self.p &= ~x

    def opSET(self, x):
        self.p |= x

    def opAND(self, x):
        self.a &= self.ByteAt(x())
        self.FlagsNZ(self.a)

    def opBIT(self, x):
        tbyte = self.ByteAt(x())
        self.p &= ~(self.ZERO | self.NEGATIVE | self.OVERFLOW)
        if (self.a & tbyte) == 0:
            self.p |= self.ZERO
        self.p |= tbyte & (self.NEGATIVE | self.OVERFLOW)

    def opROL(self, x):
        if x is None:
            tbyte = self.a
        else:
            addr = x()
            tbyte = self.ByteAt(addr)

        if self.p & self.CARRY:
            if tbyte & self.NEGATIVE:
                pass
            else:
                self.p &= ~self.CARRY
            tbyte = (tbyte << 1) | 1
        else:
            if tbyte & self.NEGATIVE:
                self.p |= self.CARRY
            tbyte = tbyte << 1
        tbyte &= self.byteMask
        self.FlagsNZ(tbyte)

        if x is None:
            self.a = tbyte
        else:
            self.memory[addr] = tbyte

    def opEOR(self, x):
        self.a ^= self.ByteAt(x())
        self.FlagsNZ(self.a)

    def opADC(self, x):
        data = self.ByteAt(x())

        if self.p & self.DECIMAL:
            halfcarry = 0
            decimalcarry = 0
            adjust0 = 0
            adjust1 = 0
            nibble0 = (data & 0xf) + (self.a & 0xf) + (self.p & self.CARRY)
            if nibble0 > 9:
                adjust0 = 6
                halfcarry = 1
            nibble1 = ((data >> 4) & 0xf) + ((self.a >> 4) & 0xf) + halfcarry
            if nibble1 > 9:
                adjust1 = 6
                decimalcarry = 1

            # the ALU outputs are not decimally adjusted
            nibble0 = nibble0 & 0xf
            nibble1 = nibble1 & 0xf
            aluresult = (nibble1 << 4) + nibble0

            # the final A contents will be decimally adjusted
            nibble0 = (nibble0 + adjust0) & 0xf
            nibble1 = (nibble1 + adjust1) & 0xf
            self.p &= ~(self.CARRY | self.OVERFLOW | self.NEGATIVE | self.ZERO)
            if aluresult == 0:
                self.p |= self.ZERO
            else:
                self.p |= aluresult & self.NEGATIVE
            if decimalcarry == 1:
                self.p |= self.CARRY
            if (~(self.a ^ data) & (self.a ^ aluresult)) & self.NEGATIVE:
                self.p |= self.OVERFLOW
            self.a = (nibble1 << 4) + nibble0
        else:
            if self.p & self.CARRY:
                tmp = 1
            else:
                tmp = 0
            result = data + self.a + tmp
            self.p &= ~(self.CARRY | self.OVERFLOW | self.NEGATIVE | self.ZERO)
            if (~(self.a ^ data) & (self.a ^ result)) & self.NEGATIVE:
                self.p |= self.OVERFLOW
            data = result
            if data > self.byteMask:
                self.p |= self.CARRY
                data &= self.byteMask
            if data == 0:
                self.p |= self.ZERO
            else:
                self.p |= data & self.NEGATIVE
            self.a = data

    def opROR(self, x):
        if x is None:
            tbyte = self.a
        else:
            addr = x()
            tbyte = self.ByteAt(addr)

        if self.p & self.CARRY:
            if tbyte & 1:
                pass
            else:
                self.p &= ~self.CARRY
            tbyte = (tbyte >> 1) | self.NEGATIVE
        else:
            if tbyte & 1:
                self.p |= self.CARRY
            tbyte = tbyte >> 1
        self.FlagsNZ(tbyte)

        if x is None:
            self.a = tbyte
        else:
            self.memory[addr] = tbyte

    def opSTA(self, x):
        self.memory[x()] = self.a

    def opSTY(self, x):
        self.memory[x()] = self.y

    def opSTX(self, y):
        self.memory[y()] = self.x

    def opCMPR(self, get_address, register_value):
        tbyte = self.ByteAt(get_address())
        self.p &= ~(self.CARRY | self.ZERO | self.NEGATIVE)
        if register_value == tbyte:
            self.p |= self.CARRY | self.ZERO
        elif register_value > tbyte:
            self.p |= self.CARRY
        self.p |= (register_value - tbyte) & self.NEGATIVE

    def opSBC(self, x):
        data = self.ByteAt(x())

        if self.p & self.DECIMAL:
            halfcarry = 1
            decimalcarry = 0
            adjust0 = 0
            adjust1 = 0

            nibble0 = (self.a & 0xf) + (~data & 0xf) + (self.p & self.CARRY)
            if nibble0 <= 0xf:
                halfcarry = 0
                adjust0 = 10
            nibble1 = ((self.a >> 4) & 0xf) + ((~data >> 4) & 0xf) + halfcarry
            if nibble1 <= 0xf:
                adjust1 = 10 << 4

            # the ALU outputs are not decimally adjusted
            aluresult = self.a + (~data & self.byteMask) + \
                (self.p & self.CARRY)

            if aluresult > self.byteMask:
                decimalcarry = 1
            aluresult &= self.byteMask

            # but the final result will be adjusted
            nibble0 = (aluresult + adjust0) & 0xf
            nibble1 = ((aluresult + adjust1) >> 4) & 0xf

            self.p &= ~(self.CARRY | self.ZERO | self.NEGATIVE | self.OVERFLOW)
            if aluresult == 0:
                self.p |= self.ZERO
            else:
                self.p |= aluresult & self.NEGATIVE
            if decimalcarry == 1:
                self.p |= self.CARRY
            if ((self.a ^ data) & (self.a ^ aluresult)) & self.NEGATIVE:
                self.p |= self.OVERFLOW
            self.a = (nibble1 << 4) + nibble0
        else:
            result = self.a + (~data & self.byteMask) + (self.p & self.CARRY)
            self.p &= ~(self.CARRY | self.ZERO | self.OVERFLOW | self.NEGATIVE)
            if ((self.a ^ data) & (self.a ^ result)) & self.NEGATIVE:
                self.p |= self.OVERFLOW
            data = result & self.byteMask
            if data == 0:
                self.p |= self.ZERO
            if result > self.byteMask:
                self.p |= self.CARRY
            self.p |= data & self.NEGATIVE
            self.a = data

    def opDECR(self, x):
        if x is None:
            tbyte = self.a
        else:
            addr = x()
            tbyte = self.ByteAt(addr)

        self.p &= ~(self.ZERO | self.NEGATIVE)
        tbyte = (tbyte - 1) & self.byteMask
        if tbyte:
            self.p |= tbyte & self.NEGATIVE
        else:
            self.p |= self.ZERO

        if x is None:
            self.a = tbyte
        else:
            self.memory[addr] = tbyte

    def opINCR(self, x):
        if x is None:
            tbyte = self.a
        else:
            addr = x()
            tbyte = self.ByteAt(addr)

        self.p &= ~(self.ZERO | self.NEGATIVE)
        tbyte = (tbyte + 1) & self.byteMask
        if tbyte:
            self.p |= tbyte & self.NEGATIVE
        else:
            self.p |= self.ZERO

        if x is None:
            self.a = tbyte
        else:
            self.memory[addr] = tbyte

    def opLDA(self, x):
        self.a = self.ByteAt(x())
        self.FlagsNZ(self.a)

    def opLDY(self, x):
        self.y = self.ByteAt(x())
        self.FlagsNZ(self.y)

    def opLDX(self, y):
        self.x = self.ByteAt(y())
        self.FlagsNZ(self.x)

    # instructions

    def inst_not_implemented(self):
        self.pc += 1

    instruct = [inst_not_implemented] * 256
    cycletime = [0] * 256
    extracycles = [0] * 256
    disassemble = [('???', 'imp')] * 256

    instruction = make_instruction_decorator(instruct, disassemble,
                                             cycletime, extracycles)

    @instruction(name="BRK", mode="imp", cycles=7)
    def inst_0x00(self):
        # pc has already been increased one
        pc = (self.pc + 1) & self.addrMask
        self.stPushWord(pc)

        self.p |= self.BREAK
        self.stPush(self.p | self.BREAK | self.UNUSED)

        self.p |= self.INTERRUPT
        self.pc = self.WordAt(self.IRQ)

    @instruction(name="ORA", mode="inx", cycles=6)
    def inst_0x01(self):
        self.opORA(self.IndirectXAddr)
        self.pc += 1

    @instruction(name="ORA", mode="zpg", cycles=3)
    def inst_0x05(self):
        self.opORA(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="ASL", mode="zpg", cycles=5)
    def inst_0x06(self):
        self.opASL(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="PHP", mode="imp", cycles=3)
    def inst_0x08(self):
        self.stPush(self.p | self.BREAK | self.UNUSED)

    @instruction(name="ORA", mode="imm", cycles=2)
    def inst_0x09(self):
        self.opORA(self.ProgramCounter)
        self.pc += 1

    @instruction(name="ASL", mode="acc", cycles=2)
    def inst_0x0a(self):
        self.opASL(None)

    @instruction(name="ORA", mode="abs", cycles=4)
    def inst_0x0d(self):
        self.opORA(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="ASL", mode="abs", cycles=6)
    def inst_0x0e(self):
        self.opASL(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BPL", mode="rel", cycles=2, extracycles=2)
    def inst_0x10(self):
        self.opBCL(self.NEGATIVE)

    @instruction(name="ORA", mode="iny", cycles=5, extracycles=1)
    def inst_0x11(self):
        self.opORA(self.IndirectYAddr)
        self.pc += 1

    @instruction(name="ORA", mode="zpx", cycles=4)
    def inst_0x15(self):
        self.opORA(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="ASL", mode="zpx", cycles=6)
    def inst_0x16(self):
        self.opASL(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="CLC", mode="imp", cycles=2)
    def inst_0x18(self):
        self.opCLR(self.CARRY)

    @instruction(name="ORA", mode="aby", cycles=4, extracycles=1)
    def inst_0x19(self):
        self.opORA(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="ORA", mode="abx", cycles=4, extracycles=1)
    def inst_0x1d(self):
        self.opORA(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="ASL", mode="abx", cycles=7)
    def inst_0x1e(self):
        self.opASL(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="JSR", mode="abs", cycles=6)
    def inst_0x20(self):
        self.stPushWord((self.pc + 1) & self.addrMask)
        self.pc = self.WordAt(self.pc)

    @instruction(name="AND", mode="inx", cycles=6)
    def inst_0x21(self):
        self.opAND(self.IndirectXAddr)
        self.pc += 1

    @instruction(name="BIT", mode="zpg", cycles=3)
    def inst_0x24(self):
        self.opBIT(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="AND", mode="zpg", cycles=3)
    def inst_0x25(self):
        self.opAND(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="ROL", mode="zpg", cycles=5)
    def inst_0x26(self):
        self.opROL(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="PLP", mode="imp", cycles=4)
    def inst_0x28(self):
        self.p = (self.stPop() | self.BREAK | self.UNUSED)

    @instruction(name="AND", mode="imm", cycles=2)
    def inst_0x29(self):
        self.opAND(self.ProgramCounter)
        self.pc += 1

    @instruction(name="ROL", mode="acc", cycles=2)
    def inst_0x2a(self):
        self.opROL(None)

    @instruction(name="BIT", mode="abs", cycles=4)
    def inst_0x2c(self):
        self.opBIT(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="AND", mode="abs", cycles=4)
    def inst_0x2d(self):
        self.opAND(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="ROL", mode="abs", cycles=6)
    def inst_0x2e(self):
        self.opROL(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BMI", mode="rel", cycles=2, extracycles=2)
    def inst_0x30(self):
        self.opBST(self.NEGATIVE)

    @instruction(name="AND", mode="iny", cycles=5, extracycles=1)
    def inst_0x31(self):
        self.opAND(self.IndirectYAddr)
        self.pc += 1

    @instruction(name="AND", mode="zpx", cycles=4)
    def inst_0x35(self):
        self.opAND(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="ROL", mode="zpx", cycles=6)
    def inst_0x36(self):
        self.opROL(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="SEC", mode="imp", cycles=2)
    def inst_0x38(self):
        self.opSET(self.CARRY)

    @instruction(name="AND", mode="aby", cycles=4, extracycles=1)
    def inst_0x39(self):
        self.opAND(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="AND", mode="abx", cycles=4, extracycles=1)
    def inst_0x3d(self):
        self.opAND(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="ROL", mode="abx", cycles=7)
    def inst_0x3e(self):
        self.opROL(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="RTI", mode="imp", cycles=6)
    def inst_0x40(self):
        self.p = (self.stPop() | self.BREAK | self.UNUSED)
        self.pc = self.stPopWord()

    @instruction(name="EOR", mode="inx", cycles=6)
    def inst_0x41(self):
        self.opEOR(self.IndirectXAddr)
        self.pc += 1

    @instruction(name="EOR", mode="zpg", cycles=3)
    def inst_0x45(self):
        self.opEOR(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="LSR", mode="zpg", cycles=5)
    def inst_0x46(self):
        self.opLSR(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="PHA", mode="imp", cycles=3)
    def inst_0x48(self):
        self.stPush(self.a)

    @instruction(name="EOR", mode="imm", cycles=2)
    def inst_0x49(self):
        self.opEOR(self.ProgramCounter)
        self.pc += 1

    @instruction(name="LSR", mode="acc", cycles=2)
    def inst_0x4a(self):
        self.opLSR(None)

    @instruction(name="JMP", mode="abs", cycles=3)
    def inst_0x4c(self):
        self.pc = self.WordAt(self.pc)

    @instruction(name="EOR", mode="abs", cycles=4)
    def inst_0x4d(self):
        self.opEOR(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="LSR", mode="abs", cycles=6)
    def inst_0x4e(self):
        self.opLSR(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BVC", mode="rel", cycles=2, extracycles=2)
    def inst_0x50(self):
        self.opBCL(self.OVERFLOW)

    @instruction(name="EOR", mode="iny", cycles=5, extracycles=1)
    def inst_0x51(self):
        self.opEOR(self.IndirectYAddr)
        self.pc += 1

    @instruction(name="EOR", mode="zpx", cycles=4)
    def inst_0x55(self):
        self.opEOR(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="LSR", mode="zpx", cycles=6)
    def inst_0x56(self):
        self.opLSR(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="CLI", mode="imp", cycles=2)
    def inst_0x58(self):
        self.opCLR(self.INTERRUPT)

    @instruction(name="EOR", mode="aby", cycles=4, extracycles=1)
    def inst_0x59(self):
        self.opEOR(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="EOR", mode="abx", cycles=4, extracycles=1)
    def inst_0x5d(self):
        self.opEOR(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="LSR", mode="abx", cycles=7)
    def inst_0x5e(self):
        self.opLSR(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="RTS", mode="imp", cycles=6)
    def inst_0x60(self):
        self.pc = self.stPopWord()
        self.pc += 1

    @instruction(name="ADC", mode="inx", cycles=6)
    def inst_0x61(self):
        self.opADC(self.IndirectXAddr)
        self.pc += 1

    @instruction(name="ADC", mode="zpg", cycles=3)
    def inst_0x65(self):
        self.opADC(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="ROR", mode="zpg", cycles=5)
    def inst_0x66(self):
        self.opROR(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="PLA", mode="imp", cycles=4)
    def inst_0x68(self):
        self.a = self.stPop()
        self.FlagsNZ(self.a)

    @instruction(name="ADC", mode="imm", cycles=2)
    def inst_0x69(self):
        self.opADC(self.ProgramCounter)
        self.pc += 1

    @instruction(name="ROR", mode="acc", cycles=2)
    def inst_0x6a(self):
        self.opROR(None)

    @instruction(name="JMP", mode="ind", cycles=5)
    def inst_0x6c(self):
        ta = self.WordAt(self.pc)
        self.pc = self.WrapAt(ta)

    @instruction(name="ADC", mode="abs", cycles=4)
    def inst_0x6d(self):
        self.opADC(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="ROR", mode="abs", cycles=6)
    def inst_0x6e(self):
        self.opROR(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BVS", mode="rel", cycles=2, extracycles=2)
    def inst_0x70(self):
        self.opBST(self.OVERFLOW)

    @instruction(name="ADC", mode="iny", cycles=5, extracycles=1)
    def inst_0x71(self):
        self.opADC(self.IndirectYAddr)
        self.pc += 1

    @instruction(name="ADC", mode="zpx", cycles=4)
    def inst_0x75(self):
        self.opADC(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="ROR", mode="zpx", cycles=6)
    def inst_0x76(self):
        self.opROR(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="SEI", mode="imp", cycles=2)
    def inst_0x78(self):
        self.opSET(self.INTERRUPT)

    @instruction(name="ADC", mode="aby", cycles=4, extracycles=1)
    def inst_0x79(self):
        self.opADC(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="ADC", mode="abx", cycles=4, extracycles=1)
    def inst_0x7d(self):
        self.opADC(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="ROR", mode="abx", cycles=7)
    def inst_0x7e(self):
        self.opROR(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="STA", mode="inx", cycles=6)
    def inst_0x81(self):
        self.opSTA(self.IndirectXAddr)
        self.pc += 1

    @instruction(name="STY", mode="zpg", cycles=3)
    def inst_0x84(self):
        self.opSTY(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="STA", mode="zpg", cycles=3)
    def inst_0x85(self):
        self.opSTA(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="STX", mode="zpg", cycles=3)
    def inst_0x86(self):
        self.opSTX(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="DEY", mode="imp", cycles=2)
    def inst_0x88(self):
        self.y -= 1
        self.y &= self.byteMask
        self.FlagsNZ(self.y)

    @instruction(name="TXA", mode="imp", cycles=2)
    def inst_0x8a(self):
        self.a = self.x
        self.FlagsNZ(self.a)

    @instruction(name="STY", mode="abs", cycles=4)
    def inst_0x8c(self):
        self.opSTY(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="STA", mode="abs", cycles=4)
    def inst_0x8d(self):
        self.opSTA(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="STX", mode="abs", cycles=4)
    def inst_0x8e(self):
        self.opSTX(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BCC", mode="rel", cycles=2, extracycles=2)
    def inst_0x90(self):
        self.opBCL(self.CARRY)

    @instruction(name="STA", mode="iny", cycles=6)
    def inst_0x91(self):
        self.opSTA(self.IndirectYAddr)
        self.pc += 1

    @instruction(name="STY", mode="zpx", cycles=4)
    def inst_0x94(self):
        self.opSTY(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="STA", mode="zpx", cycles=4)
    def inst_0x95(self):
        self.opSTA(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="STX", mode="zpy", cycles=4)
    def inst_0x96(self):
        self.opSTX(self.ZeroPageYAddr)
        self.pc += 1

    @instruction(name="TYA", mode="imp", cycles=2)
    def inst_0x98(self):
        self.a = self.y
        self.FlagsNZ(self.a)

    @instruction(name="STA", mode="aby", cycles=5)
    def inst_0x99(self):
        self.opSTA(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="TXS", mode="imp", cycles=2)
    def inst_0x9a(self):
        self.sp = self.x

    @instruction(name="STA", mode="abx", cycles=5)
    def inst_0x9d(self):
        self.opSTA(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="LDY", mode="imm", cycles=2)
    def inst_0xa0(self):
        self.opLDY(self.ProgramCounter)
        self.pc += 1

    @instruction(name="LDA", mode="inx", cycles=6)
    def inst_0xa1(self):
        self.opLDA(self.IndirectXAddr)
        self.pc += 1

    @instruction(name="LDX", mode="imm", cycles=2)
    def inst_0xa2(self):
        self.opLDX(self.ProgramCounter)
        self.pc += 1

    @instruction(name="LDY", mode="zpg", cycles=3)
    def inst_0xa4(self):
        self.opLDY(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="LDA", mode="zpg", cycles=3)
    def inst_0xa5(self):
        self.opLDA(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="LDX", mode="zpg", cycles=3)
    def inst_0xa6(self):
        self.opLDX(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="TAY", mode="imp", cycles=2)
    def inst_0xa8(self):
        self.y = self.a
        self.FlagsNZ(self.y)

    @instruction(name="LDA", mode="imm", cycles=2)
    def inst_0xa9(self):
        self.opLDA(self.ProgramCounter)
        self.pc += 1

    @instruction(name="TAX", mode="imp", cycles=2)
    def inst_0xaa(self):
        self.x = self.a
        self.FlagsNZ(self.x)

    @instruction(name="LDY", mode="abs", cycles=4)
    def inst_0xac(self):
        self.opLDY(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="LDA", mode="abs", cycles=4)
    def inst_0xad(self):
        self.opLDA(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="LDX", mode="abs", cycles=4)
    def inst_0xae(self):
        self.opLDX(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BCS", mode="rel", cycles=2, extracycles=2)
    def inst_0xb0(self):
        self.opBST(self.CARRY)

    @instruction(name="LDA", mode="iny", cycles=5, extracycles=1)
    def inst_0xb1(self):
        self.opLDA(self.IndirectYAddr)
        self.pc += 1

    @instruction(name="LDY", mode="zpx", cycles=4)
    def inst_0xb4(self):
        self.opLDY(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="LDA", mode="zpx", cycles=4)
    def inst_0xb5(self):
        self.opLDA(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="LDX", mode="zpy", cycles=4)
    def inst_0xb6(self):
        self.opLDX(self.ZeroPageYAddr)
        self.pc += 1

    @instruction(name="CLV", mode="imp", cycles=2)
    def inst_0xb8(self):
        self.opCLR(self.OVERFLOW)

    @instruction(name="LDA", mode="aby", cycles=4, extracycles=1)
    def inst_0xb9(self):
        self.opLDA(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="TSX", mode="imp", cycles=2)
    def inst_0xba(self):
        self.x = self.sp
        self.FlagsNZ(self.x)

    @instruction(name="LDY", mode="abx", cycles=4, extracycles=1)
    def inst_0xbc(self):
        self.opLDY(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="LDA", mode="abx", cycles=4, extracycles=1)
    def inst_0xbd(self):
        self.opLDA(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="LDX", mode="aby", cycles=4, extracycles=1)
    def inst_0xbe(self):
        self.opLDX(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="CPY", mode="imm", cycles=2)
    def inst_0xc0(self):
        self.opCMPR(self.ProgramCounter, self.y)
        self.pc += 1

    @instruction(name="CMP", mode="inx", cycles=6)
    def inst_0xc1(self):
        self.opCMPR(self.IndirectXAddr, self.a)
        self.pc += 1

    @instruction(name="CPY", mode="zpg", cycles=3)
    def inst_0xc4(self):
        self.opCMPR(self.ZeroPageAddr, self.y)
        self.pc += 1

    @instruction(name="CMP", mode="zpg", cycles=3)
    def inst_0xc5(self):
        self.opCMPR(self.ZeroPageAddr, self.a)
        self.pc += 1

    @instruction(name="DEC", mode="zpg", cycles=5)
    def inst_0xc6(self):
        self.opDECR(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="INY", mode="imp", cycles=2)
    def inst_0xc8(self):
        self.y += 1
        self.y &= self.byteMask
        self.FlagsNZ(self.y)

    @instruction(name="CMP", mode="imm", cycles=2)
    def inst_0xc9(self):
        self.opCMPR(self.ProgramCounter, self.a)
        self.pc += 1

    @instruction(name="DEX", mode="imp", cycles=2)
    def inst_0xca(self):
        self.x -= 1
        self.x &= self.byteMask
        self.FlagsNZ(self.x)

    @instruction(name="CPY", mode="abs", cycles=4)
    def inst_0xcc(self):
        self.opCMPR(self.AbsoluteAddr, self.y)
        self.pc += 2

    @instruction(name="CMP", mode="abs", cycles=4)
    def inst_0xcd(self):
        self.opCMPR(self.AbsoluteAddr, self.a)
        self.pc += 2

    @instruction(name="DEC", mode="abs", cycles=3)
    def inst_0xce(self):
        self.opDECR(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BNE", mode="rel", cycles=2, extracycles=2)
    def inst_0xd0(self):
        self.opBCL(self.ZERO)

    @instruction(name="CMP", mode="iny", cycles=5, extracycles=1)
    def inst_0xd1(self):
        self.opCMPR(self.IndirectYAddr, self.a)
        self.pc += 1

    @instruction(name="CMP", mode="zpx", cycles=4)
    def inst_0xd5(self):
        self.opCMPR(self.ZeroPageXAddr, self.a)
        self.pc += 1

    @instruction(name="DEC", mode="zpx", cycles=6)
    def inst_0xd6(self):
        self.opDECR(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="CLD", mode="imp", cycles=2)
    def inst_0xd8(self):
        self.opCLR(self.DECIMAL)

    @instruction(name="CMP", mode="aby", cycles=4, extracycles=1)
    def inst_0xd9(self):
        self.opCMPR(self.AbsoluteYAddr, self.a)
        self.pc += 2

    @instruction(name="CMP", mode="abx", cycles=4, extracycles=1)
    def inst_0xdd(self):
        self.opCMPR(self.AbsoluteXAddr, self.a)
        self.pc += 2

    @instruction(name="DEC", mode="abx", cycles=7)
    def inst_0xde(self):
        self.opDECR(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="CPX", mode="imm", cycles=2)
    def inst_0xe0(self):
        self.opCMPR(self.ProgramCounter, self.x)
        self.pc += 1

    @instruction(name="SBC", mode="inx", cycles=6)
    def inst_0xe1(self):
        self.opSBC(self.IndirectXAddr)
        self.pc += 1

    @instruction(name="CPX", mode="zpg", cycles=3)
    def inst_0xe4(self):
        self.opCMPR(self.ZeroPageAddr, self.x)
        self.pc += 1

    @instruction(name="SBC", mode="zpg", cycles=3)
    def inst_0xe5(self):
        self.opSBC(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="INC", mode="zpg", cycles=5)
    def inst_0xe6(self):
        self.opINCR(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="INX", mode="imp", cycles=2)
    def inst_0xe8(self):
        self.x += 1
        self.x &= self.byteMask
        self.FlagsNZ(self.x)

    @instruction(name="SBC", mode="imm", cycles=2)
    def inst_0xe9(self):
        self.opSBC(self.ProgramCounter)
        self.pc += 1

    @instruction(name="NOP", mode="imp", cycles=2)
    def inst_0xea(self):
        pass

    @instruction(name="CPX", mode="abs", cycles=4)
    def inst_0xec(self):
        self.opCMPR(self.AbsoluteAddr, self.x)
        self.pc += 2

    @instruction(name="SBC", mode="abs", cycles=4)
    def inst_0xed(self):
        self.opSBC(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="INC", mode="abs", cycles=6)
    def inst_0xee(self):
        self.opINCR(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="BEQ", mode="rel", cycles=2, extracycles=2)
    def inst_0xf0(self):
        self.opBST(self.ZERO)

    @instruction(name="SBC", mode="iny", cycles=5, extracycles=1)
    def inst_0xf1(self):
        self.opSBC(self.IndirectYAddr)
        self.pc += 1

    @instruction(name="SBC", mode="zpx", cycles=4)
    def inst_0xf5(self):
        self.opSBC(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="INC", mode="zpx", cycles=6)
    def inst_0xf6(self):
        self.opINCR(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="SED", mode="imp", cycles=2)
    def inst_0xf8(self):
        self.opSET(self.DECIMAL)

    @instruction(name="SBC", mode="aby", cycles=4, extracycles=1)
    def inst_0xf9(self):
        self.opSBC(self.AbsoluteYAddr)
        self.pc += 2

    @instruction(name="SBC", mode="abx", cycles=4, extracycles=1)
    def inst_0xfd(self):
        self.opSBC(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="INC", mode="abx", cycles=7)
    def inst_0xfe(self):
        self.opINCR(self.AbsoluteXAddr)
        self.pc += 2





class MPU(mpu6502_MPU):
    def __init__(self, *args, **kwargs):
        mpu6502_MPU.__init__(self, *args, **kwargs)
        self.name = '65C02'
        self.waiting = False
        self.done=False

    def step(self):
        if self.waiting:
            self.processorCycles += 1
        elif self.done:
            return None
        else:
            mpu6502_MPU.step(self)
        return self

    # Make copies of the lists
    instruct = mpu6502_MPU.instruct[:]
    cycletime = mpu6502_MPU.cycletime[:]
    extracycles = mpu6502_MPU.extracycles[:]
    disassemble = mpu6502_MPU.disassemble[:]

    instruction = make_instruction_decorator(instruct, disassemble,
                                             cycletime, extracycles)

    # addressing modes

    def ZeroPageIndirectAddr(self):
        return self.WordAt(255 & (self.ByteAt(self.pc)))

    def IndirectAbsXAddr(self):
        return (self.WordAt(self.pc) + self.x) & self.addrMask

    # operations

    def opRMB(self, x, mask):
        address = x()
        self.memory[address] &= mask

    def opSMB(self, x, mask):
        address = x()
        self.memory[address] |= mask

    def opSTZ(self, x):
        self.memory[x()] = 0x00

    def opTSB(self, x):
        address = x()
        m = self.memory[address]
        self.p &= ~self.ZERO
        z = m & self.a
        if z == 0:
            self.p |= self.ZERO
        self.memory[address] = m | self.a

    def opTRB(self, x):
        address = x()
        m = self.memory[address]
        self.p &= ~self.ZERO
        z = m & self.a
        if z == 0:
            self.p |= self.ZERO
        self.memory[address] = m & ~self.a

    # instructions

    @instruction(name="BRK", mode="imp", cycles=7)
    def inst_0x00(self):
        # pc has already been increased one
        pc = (self.pc + 1) & self.addrMask
        self.stPushWord(pc)

        self.p |= self.BREAK
        self.stPush(self.p | self.BREAK | self.UNUSED)

        self.p |= self.INTERRUPT
        self.pc = self.WordAt(self.IRQ)

        # 65C02 clears decimal flag, NMOS 6502 does not
        self.p &= ~self.DECIMAL

    @instruction(name="TSB", mode="zpg", cycles=5)
    def inst_0x04(self):
        self.opTSB(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="RMB0", mode="zpg", cycles=5)
    def inst_0x07(self):
        self.opRMB(self.ZeroPageAddr, 0xFE)
        self.pc += 1

    @instruction(name="TSB", mode="abs", cycles=6)
    def inst_0x0c(self):
        self.opTSB(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="ORA", mode="zpi", cycles=5)
    def inst_0x12(self):
        self.opORA(self.ZeroPageIndirectAddr)
        self.pc += 1

    @instruction(name="TRB", mode="zpg", cycles=5)
    def inst_0x14(self):
        self.opTRB(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="RMB1", mode="zpg", cycles=5)
    def inst_0x17(self):
        self.opRMB(self.ZeroPageAddr, 0xFD)
        self.pc += 1

    @instruction(name="INC", mode="acc", cycles=2)
    def inst_0x1a(self):
        self.opINCR(None)

    @instruction(name="TRB", mode="abs", cycles=6)
    def inst_0x1c(self):
        self.opTRB(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="RMB2", mode="zpg", cycles=5)
    def inst_0x27(self):
        self.opRMB(self.ZeroPageAddr, 0xFB)
        self.pc += 1

    @instruction(name="AND", mode="zpi", cycles=5)
    def inst_0x32(self):
        self.opAND(self.ZeroPageIndirectAddr)
        self.pc += 1

    @instruction(name="BIT", mode="zpx", cycles=4)
    def inst_0x34(self):
        self.opBIT(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="RMB3", mode="zpg", cycles=5)
    def inst_0x37(self):
        self.opRMB(self.ZeroPageAddr, 0xF7)
        self.pc += 1

    @instruction(name="DEC", mode="acc", cycles=2)
    def inst_0x3a(self):
        self.opDECR(None)

    @instruction(name="BIT", mode="abx", cycles=4)
    def inst_0x3c(self):
        self.opBIT(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="RMB4", mode="zpg", cycles=5)
    def inst_0x47(self):
        self.opRMB(self.ZeroPageAddr, 0xEF)
        self.pc += 1

    @instruction(name="EOR", mode="zpi", cycles=5)
    def inst_0x52(self):
        self.opEOR(self.ZeroPageIndirectAddr)
        self.pc += 1

    @instruction(name="RMB5", mode="zpg", cycles=5)
    def inst_0x57(self):
        self.opRMB(self.ZeroPageAddr, 0xDF)
        self.pc += 1

    @instruction(name="PHY", mode="imp", cycles=3)
    def inst_0x5a(self):
        self.stPush(self.y)

    @instruction(name="STZ", mode="imp", cycles=3)
    def inst_0x64(self):
        self.opSTZ(self.ZeroPageAddr)
        self.pc += 1

    @instruction(name="RMB6", mode="zpg", cycles=5)
    def inst_0x67(self):
        self.opRMB(self.ZeroPageAddr, 0xBF)
        self.pc += 1

    @instruction(name="JMP", mode="ind", cycles=6)
    def inst_0x6c(self):
        ta = self.WordAt(self.pc)
        self.pc = self.WordAt(ta)

    @instruction(name="ADC", mode="zpi", cycles=5)
    def inst_0x72(self):
        self.opADC(self.ZeroPageIndirectAddr)
        self.pc += 1

    @instruction(name="STZ", mode="zpx", cycles=4)
    def inst_0x74(self):
        self.opSTZ(self.ZeroPageXAddr)
        self.pc += 1

    @instruction(name="RMB7", mode="zpg", cycles=5)
    def inst_0x77(self):
        self.opRMB(self.ZeroPageAddr, 0x7F)
        self.pc += 1

    @instruction(name="PLY", mode="imp", cycles=4)
    def inst_0x7a(self):
        self.y = self.stPop()
        self.FlagsNZ(self.y)

    @instruction(name="JMP", mode="iax", cycles=6)
    def inst_0x7c(self):
        self.pc = self.WordAt(self.IndirectAbsXAddr())

    @instruction(name="BRA", mode="rel", cycles=1, extracycles=1)
    def inst_0x80(self):
        self.BranchRelAddr()

    @instruction(name="SMB0", mode="zpg", cycles=5)
    def inst_0x87(self):
        self.opSMB(self.ZeroPageAddr, 0x01)
        self.pc += 1

    @instruction(name="BIT", mode="imm", cycles=2)
    def inst_0x89(self):
        # This instruction (BIT #$12) does not use opBIT because in the
        # immediate mode, BIT only affects the Z flag.
        tbyte = self.ImmediateByte()
        self.p &= ~(self.ZERO)
        if (self.a & tbyte) == 0:
            self.p |= self.ZERO
        self.pc += 1

    @instruction(name="STA", mode="zpi", cycles=5)
    def inst_0x92(self):
        self.opSTA(self.ZeroPageIndirectAddr)
        self.pc += 1

    @instruction(name="SMB1", mode="zpg", cycles=5)
    def inst_0x97(self):
        self.opSMB(self.ZeroPageAddr, 0x02)
        self.pc += 1

    @instruction(name="STZ", mode="abs", cycles=4)
    def inst_0x9c(self):
        self.opSTZ(self.AbsoluteAddr)
        self.pc += 2

    @instruction(name="STZ", mode="abx", cycles=5)
    def inst_0x9e(self):
        self.opSTZ(self.AbsoluteXAddr)
        self.pc += 2

    @instruction(name="SMB2", mode="zpg", cycles=5)
    def inst_0xa7(self):
        self.opSMB(self.ZeroPageAddr, 0x04)
        self.pc += 1

    @instruction(name="LDA", mode="zpi", cycles=5)
    def inst_0xb2(self):
        self.opLDA(self.ZeroPageIndirectAddr)
        self.pc += 1

    @instruction(name="SMB3", mode="zpg", cycles=5)
    def inst_0xb7(self):
        self.opSMB(self.ZeroPageAddr, 0x08)
        self.pc += 1

    @instruction(name="SMB4", mode="zpg", cycles=5)
    def inst_0xc7(self):
        self.opSMB(self.ZeroPageAddr, 0x10)
        self.pc += 1

    @instruction(name="WAI", mode='imp', cycles=3)
    def inst_0xcb(self):
        self.waiting = True

    @instruction(name="CMP", mode='zpi', cycles=5)
    def inst_0xd2(self):
        self.opCMPR(self.ZeroPageIndirectAddr, self.a)
        self.pc += 1

    @instruction(name="SMB5", mode="zpg", cycles=5)
    def inst_0xd7(self):
        self.opSMB(self.ZeroPageAddr, 0x20)
        self.pc += 1

    @instruction(name="PHX", mode="imp", cycles=3)
    def inst_0xda(self):
        self.stPush(self.x)

    @instruction(name="SMB6", mode="zpg", cycles=5)
    def inst_0xe7(self):
        self.opSMB(self.ZeroPageAddr, 0x40)
        self.pc += 1

    @instruction(name="SBC", mode="zpi", cycles=5)
    def inst_0xf2(self):
        self.opSBC(self.ZeroPageIndirectAddr)
        self.pc += 1

    @instruction(name="SMB7", mode="zpg", cycles=5)
    def inst_0xf7(self):
        self.opSMB(self.ZeroPageAddr, 0x80)
        self.pc += 1

    @instruction(name="PLX", mode="imp", cycles=4)
    def inst_0xfa(self):
        self.x = self.stPop()
        self.FlagsNZ(self.x)
        
    @instruction(name="STP", mode="imp", cycles=3)
    def inst_0xdb(self):
        self.done=True
        
                
mem=ObservableMemory()
cpu=MPU(memory=mem)
dis=Disassembler(cpu)
assmbl=Assembler(cpu)


class loadfiles:
    def __init__(self, mem):
        self.mem=mem
        self.filedata=[None,'','']
        
    def _start(self, *args):
        self.loadfilewin = tkinter.Tk()
        self.loadfilewin.title("Load binary")
        self.loadfilewin.minsize(300,20)
        self.loadfilewin.resizable(width=False, height=False)
        self.loadfilewin.iconphoto(False, PhotoImage(master=self.loadfilewin, file = 'res/65c02.png'))
        
        self.lab_filename=Label(self.loadfilewin) 
        self.lab_filename.grid(row=1,column=0,pady=10,padx=10) 
        
        but_bin=Button(self.loadfilewin,text="Load",command=self.loadbin)
        but_bin.grid(row=0,column=0,pady=10,padx=10)  
        
        but_kill=Button(self.loadfilewin,text="Close",command=lambda: self.loadfilewin.destroy())
        but_kill.grid(row=0,column=1,pady=10,padx=10)  
        
        
        self.loadfilewin.mainloop() 
        
    def start(self, frame):
        self.lab_filename=Label(frame) 
        self.lab_filename.grid(row=0,column=5,pady=10,padx=10) 
        
        but_bin=Button(frame,text="Load binary",command=self.loadbin)
        but_bin.grid(row=0,column=6,pady=10,padx=10)
        
        
        return frame   
        
    def get_filedata(self):
        return self.filedata
    
    def loadbin(self):
        self.filedata=None
        
        start=tkinter.simpledialog.askstring(title="Address",prompt="Load address")
        
        try:
            if start[0].isdigit():
                start=int(start)
            elif start[0]=="#":
                start=int(start[1:])
            elif start[0]=="$":
                start=int(start[1:],16)
            elif start[0]=="%":
                start=int(start[1:],2)
            else:
                messagebox.showerror("Error","Invalid address.")
                return  
        except TypeError:
            messagebox.showerror("Error","Ensure load address is set.")
            return  
            
            
        if start>=65536:
            messagebox.showerror("Error","Address cannot be > 65535.")
            return  

            
        try:
            f=askopenfile(mode='rb', initialfile="untitled.s",defaultextension=".s",filetypes=[("All Files","*.*"),("Binary files","*.bin")])       
            name=f.name
            f.close()
            
            with open(name,'rb') as file:
                filedata=list(file.read()) 

            for n in range(start,len(filedata)+start):
                self.mem[n]=filedata[n-start]+0x10000
                
            self.lab_filename.config(text=f.name)
            
            self.filedata=[filedata,'bin',name]
        except AttributeError:
            pass

       
        
class dumpmem:
    def __init__(self, mem):
        self.mem=mem
        
    def start(self, frame):
        lab_start=Label(frame,text="Start address") 
        lab_start.grid(row=0,column=0,pady=2,padx=2)  
        
        self.start = tk.Text(frame, height = 1, width = 10)
        self.start.grid(row=1,column=0,pady=2,padx=2)  
        
        lab_end=Label(frame,text="End address") 
        lab_end.grid(row=2,column=0,pady=2,padx=2)  
        
        self.end = tk.Text(frame, height = 1, width = 10)
        self.end.grid(row=3,column=0,pady=2,padx=2)  
        
        but_dev=Button(frame,text="Dump",command=self.actdump)
        but_dev.grid(row=4,column=0,pady=2,padx=2)  
        
        self.txtout=tkinter.scrolledtext.ScrolledText(frame, bg="white", width = 40, height = 10, )
        self.txtout.grid(row=5,column=0,pady=2,padx=2)  
        
        self.txtout.focus()
        
        self.txtout.configure(state ='disabled')
        
        return frame
        
    def actdump(self):
        start = self.start.get(1.0, "end-1c")
        end = self.end.get(1.0, "end-1c")
        
        try:
            if start[0].isdigit():
                start=int(start)
            elif start[0]=="#":
                start=int(start[1:])
            elif start[0]=="$":
                start=int(start[1:],16)
            elif start[0]=="%":
                start=int(start[1:],2)
            else:
                messagebox.showerror("Error","Invalid address.")
                return  
        except TypeError:
            messagebox.showerror("Error","Ensure valid start address is set.")
            return  
        except ValueError:
            messagebox.showerror("Error","Ensure valid start address is set.")
            return  
        
        try:
            if end[0].isdigit():
                end=int(end)
            elif end[0]=="#":
                end=int(end[1:])
            elif end[0]=="$":
                end=int(end[1:],16)
            elif end[0]=="%":
                end=int(end[1:],2)
            else:
                messagebox.showerror("Error","Invalid address.")
                return  
        except TypeError:
            messagebox.showerror("Error","Ensure end address is set.")
            return  
        except ValueError:
            messagebox.showerror("Error","Ensure valid start address is set.")
            return  
            
        if end<=start:
            messagebox.showerror(text="Start address must be greater than end address.")
            return
        
        if end>=65536:
            messagebox.showerror(text="Address must not be greater than 65535.")
            return
        
        string=''
        for n in range(start,end+1):
            x=str(n)+": "+str(self.mem[n])+"\n"
            string+=x
            
        self.txtout.configure(state ='normal')
        self.txtout.delete("1.0","end")
        self.txtout.insert(tk.INSERT,string)          
        # Making the text read only
        self.txtout.configure(state ='disabled')
        
        
class disassmbl:
    def __init__(self, mem):
        self.mem=mem
        
    def start(self, frame):
        lab_start=Label(frame,text="Start address") 
        lab_start.grid(row=0,column=0,pady=2,padx=2)  
        
        self.start = tk.Text(frame, height = 1, width = 10)
        self.start.grid(row=1,column=0,pady=2,padx=2)  
        
        lab_end=Label(frame,text="End address") 
        lab_end.grid(row=2,column=0,pady=2,padx=2)  
        
        self.end = tk.Text(frame, height = 1, width = 10)
        self.end.grid(row=3,column=0,pady=2,padx=2)  
        
        but_dev=Button(frame,text="Disassemble",command=self.actdis)
        but_dev.grid(row=4,column=0,pady=2,padx=2)  
        
        self.txtout=tkinter.scrolledtext.ScrolledText(frame, bg="white", width = 40, height = 10, )
        self.txtout.grid(row=5,column=0,pady=2,padx=2)  
        
        self.txtout.focus()
        
        self.txtout.configure(state ='disabled')
        
        return frame
        
    def on_closing(self):
        self.diswindow.destroy()
        
    def disassemble(self, start,end):
        
        string=''
        
        n=start
        for _ in range(start,end+1):
            (length, disasm)=dis.instruction_at(n)
            x=str(n)+": "+disasm+"\n"
            n+=length
            string+=x
        
        self.txtout.configure(state ='normal')
        self.txtout.delete("1.0","end")
        self.txtout.insert(tk.INSERT,string)          
        # Making the text read only
        self.txtout.configure(state ='disabled')
        
    def actdis(self):
        start = self.start.get(1.0, "end-1c")
        end = self.end.get(1.0, "end-1c")
        
        try:
            if start[0].isdigit():
                start=int(start)
            elif start[0]=="#":
                start=int(start[1:])
            elif start[0]=="$":
                start=int(start[1:],16)
            elif start[0]=="%":
                start=int(start[1:],2)
            else:
                messagebox.showerror("Error","Invalid address.")
                return  
        except TypeError:
            messagebox.showerror("Error","Ensure start address is set.")
            return 
        except ValueError:
            messagebox.showerror("Error","Ensure valid start address is set.")
            return  
            
        try:
            if end[0].isdigit():
                end=int(end)
            elif end[0]=="#":
                end=int(end[1:])
            elif end[0]=="$":
                end=int(end[1:],16)
            elif end[0]=="%":
                end=int(end[1:],2)
            else:
                messagebox.showerror("Error","Invalid address.")
                return  
        except TypeError:
            messagebox.showerror("Error","Ensure end address is set.")
            return  
        except ValueError:
            messagebox.showerror("Error","Ensure valid start address is set.")
            return  
        
        if end<=start:
            messagebox.showerror("Error","Start address must be greater than end address.")
            return
        
        if end>=65536:
            messagebox.showerror("Error","Address must not be greater than 65535.")
            return
        
        
        self.disassemble(start,end)
        
class editmem:
    def __init__(self, mem):
        self.mem=mem
        
    def start(self, frame):
        lab_addr=Label(frame,text="Address") 
        lab_addr.grid(row=0,column=0,pady=2,padx=2)  
        
        self.addr = tk.Text(frame, height = 1, width = 10)
        self.addr.grid(row=1,column=0,pady=2,padx=2)  
        
        lab_end=Label(frame,text="Value") 
        lab_end.grid(row=0,column=1,pady=2,padx=2)  
        
        self.val = tk.Text(frame, height = 1, width = 10)
        self.val.grid(row=1,column=1,pady=2,padx=2)  
        
        but_dev=Button(frame,text="Write",command=self.actedit)
        but_dev.grid(row=2,column=0,pady=2,padx=2)  
        
        return frame

        
    def actedit(self):
        addr = self.addr.get(1.0, "end-1c")
        val = self.val.get(1.0, "end-1c")
        
        try:
            if addr[0].isdigit():
                addr=int(addr)
            elif addr[0]=="#":
                addr=int(addr[1:])
            elif addr[0]=="$":
                addr=int(addr[1:],16)
            elif addr[0]=="%":
                addr=int(addr[1:],2)
        except:
            messagebox.showerror("Error","Missing input value.")
            return
            
        try:
            if val[0].isdigit():
                val=int(val)
            elif val[0]=="#":
                val=int(val[1:])
            elif val[0]=="$":
                val=int(val[1:],16)
            elif val[0]=="%":
                val=int(val[1:],2)
        except:
            messagebox.showerror("Error","Missing input value.")
            return
            
        if addr>=65536:
            messagebox.showerror("Error","Address must not be greater than 65535.")
            return
        
        if val>=256:
            messagebox.showerror("Error","Value must not be greater than 255.")
            return
        
        self.mem[addr]=val
        
class readbyte:
    def __init__(self, mem):
        self.mem=mem
        
    def start(self, frame):
        lab_addr=Label(frame,text="Address") 
        lab_addr.grid(row=0,column=0,pady=2,padx=2) 
        
        self.addr = tk.Text(frame, height = 1, width = 10)
        self.addr.grid(row=1,column=0,pady=2,padx=2)
        
        but_dev=Button(frame,text="Read",command=self.actedit)
        but_dev.grid(row=3,column=0,pady=2,padx=2)
        
        self.lab_message=Label(frame) 
        self.lab_message.grid(row=2,column=0,pady=2,padx=2)   
        
        return frame

        
    def actedit(self):
        addr = self.addr.get(1.0, "end-1c")
        
        try:
            if addr[0].isdigit():
                addr=int(addr)
            elif addr[0]=="#":
                addr=int(addr[1:])
            elif addr[0]=="$":
                addr=int(addr[1:],16)
            elif addr[0]=="%":
                addr=int(addr[1:],2)
            if addr>=65536:
                messagebox.showerror("Error","Address must not be greater than 65535.")
                return
        except:
            messagebox.showerror("Error","Missing input value.")
            return
        

        self.lab_message.config(text=str(addr)+": "+str(self.mem[addr]))
        
class editor:
    def __init__(self,mem,infowin,files):
        self.settings={}
        self.currentfile=""
        self.mem=mem
        self.infowin=infowin
        self.files=files
        
    def start(self, buttons, texteditor):
        self.txtinput=tkinter.scrolledtext.ScrolledText(texteditor, bg="white", undo=True, maxundo=-1)
        self.txtinput.grid(row=0,column=0,pady=10,padx=10)

        self.txtinput.focus()

        saveasbtn=tkinter.Button(buttons, text="Save As", relief="raised", command=self.saveas)
        saveasbtn.grid(row=0,column=1,pady=2,padx=2,sticky="w")

        openfilebtn=tkinter.Button(buttons, text="Open File", relief="raised", command=self.openfile)
        openfilebtn.grid(row=0,column=0,pady=2,padx=2,sticky="w")

        savefilebtn=tkinter.Button(buttons,  text="Save File", relief="raised", command=self.savecurrent)
        savefilebtn.grid(row=0,column=2,pady=2,padx=2,sticky="w")
        
        newfilebtn=tkinter.Button(buttons,   text="New", relief="raised", command=self.newwin)
        newfilebtn.grid(row=0,column=3,pady=2,padx=2,sticky="w")
        
        quickasmbtn=tkinter.Button(buttons, text="Assemble", relief="raised", command=self.quickasm)
        quickasmbtn.grid(row=0,column=4,pady=2,padx=2,sticky="w")

        return buttons,texteditor
    
    def _start(self):
        self.window = tkinter.Tk()
        self.window.title("Editor")
        self.window.resizable(width=False, height=False)
        self.window.iconphoto(False, PhotoImage(master=self.window, file = 'res/65c02.png'))
        
        buttons = Frame(self.window)
        texteditor = Frame(self.window)
        buttons.grid(row=0,column=0,pady=10,padx=10,sticky="w")
        texteditor.grid(row=1,column=0,pady=10,padx=10)

        self.txtinput=tkinter.scrolledtext.ScrolledText(texteditor, bg="white", undo=True, maxundo=-1)
        self.txtinput.grid(row=0,column=0,pady=10,padx=10)

        self.txtinput.focus()

        saveasbtn=tkinter.Button(buttons,  text="Save As", relief="raised", command=self.saveas)
        saveasbtn.grid(row=0,column=1,pady=2,padx=2,sticky="w")

        openfilebtn=tkinter.Button(buttons,  text="Open File", relief="raised", command=self.openfile)
        openfilebtn.grid(row=0,column=0,pady=2,padx=2,sticky="w")

        savefilebtn=tkinter.Button(buttons,  text="Save File", relief="raised", command=self.savecurrent)
        savefilebtn.grid(row=0,column=2,pady=2,padx=2,sticky="w")
        
        newfilebtn=tkinter.Button(buttons,  text="New", relief="raised", command=self.newwin)
        newfilebtn.grid(row=0,column=3,pady=2,padx=2,sticky="w")
        
        quickasmbtn=tkinter.Button(buttons,   text="Assemble", relief="raised", command=self.quickasm)
        quickasmbtn.grid(row=0,column=4,pady=2,padx=2,sticky="w")

        self.window.protocol("WM_DELETE_WINDOW",self.on_closing)
        
        self.window.bind("<Control-Shift-S>", self.saveas)
        self.window.bind("<Control-s>", self.savecurrent)
        self.window.bind("<Control-o>", self.openfile)
        self.window.bind("<Control-b>", self.quickasm)
        self.window.bind("<Control-Shift-O>", self.files._start)
        self.window.bind("<Control-n>", self.newwin)
        self.window.mainloop()
        
    def newwin(self, *args):
        newobj = self.__class__(self.mem, self.infowin, self.files)
        newobj._start()

    def quickasm(self, *args):
        try:
            text=self.txtinput.get("1.0","end") #Get input text box
            
            f=open(self.currentfile,"w")    
            f.write(text)
            f.close()
        except AttributeError:
            pass
        except FileNotFoundError:
            messagebox.showerror("Error","File not open")
            return 
        
        if len(self.currentfile)==0:
            messagebox.showerror("Error","File not open")
            return
        name=self.currentfile.split(".")
        name[0]=name[0].split("/")[-1]
        asmname=name[0]+"."+name[1]
        binname=name[0]+".bin"
        operation="vasm6502_oldstyle -Fbin -dotdir -wdc02 \""+asmname+"\" -o \""+binname+"\""

        oplist=shlex.split(operation)
        process = subprocess.run(oplist, 
                         stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE,
                         universal_newlines=True)
        output=str(process.stdout)+str(process.stderr)
        Thread(target=lambda: self.infowin.setval(output)).start()
        if process.returncode==1:
            return
        
        try:            
            with open(binname,'rb') as file:
                filedata=list(file.read())   
            
        except UnicodeDecodeError:
            messagebox.showerror("Error","Incorrect file type")
            return
        
        start=int("0x"+output.split("seg")[1].split("(")[0],16)
        
        for n in range(start,len(filedata)+start):
            self.mem[n]=filedata[n-start]+0x10000

    def saveas(self, *args):
        try:
            text=self.txtinput.get("1.0","end") #Get input text box
            
            f=asksaveasfile(initialfile="untitled.s",defaultextension=".s",filetypes=[("All Files","*.*"),("Text Documents","*.txt")])       
            self.currentfile=f.name
            f.write(text)
            f.close()
            
            self.window.title("Editor"+" - "+self.currentfile)
        except AttributeError:
            pass
        except FileNotFoundError:
            pass
            
    def savecurrent(self, *args):
        try:
            text=self.txtinput.get("1.0","end") #Get input text box
            
            f=open(self.currentfile,"w")    
            f.write(text)
            f.close()
        except AttributeError:
            pass
        except FileNotFoundError:
            messagebox.showerror("Error","File not open")
        
    def openfile(self, *args):
        try:            
            f=askopenfile(initialfile="untitled.txt",defaultextension=".s",filetypes=[("All Files","*.*"),("Text Documents","*.txt")])       
            self.currentfile=f.name
            text=self.txtinput.delete("1.0","end") #delete input text box
            self.txtinput.insert(INSERT,f.read())
            f.close()

            self.window.title("Editor"+" - "+self.currentfile)
            
        except AttributeError:
            pass
        except FileNotFoundError:
            pass
        except UnicodeDecodeError:
            messagebox.showerror("Error","Incorrect file type")
            return

    def on_closing(self):
        self.window.destroy()


class runclass:
    def __init__(self, cpu, mem):
        self.cpu=cpu
        self._kill = Event()
        self._pause = Event()
        self.mem=mem
        self.text=[]
        self.txtout=None
        self.totaldevices=[]
        self.result=str(cpu)
        self.specialwrites=None
        self.clockhandlers=[]
        self.clock_kill = Event()
        
        self.clock_interval=1000 #1/x s 
        
        Thread(target=self.clockhandler).start()
        
    def runcpu(self):
        self.text=[]
        cpu=self.cpu
        cpu.reset()
        while True:
            result=cpu.step()
            self.result=result
            if result==None:
                messagebox.showinfo("Execution","Execution finished")
                break
            
            is_killed = self._kill.wait(0)
            if is_killed:
                self._kill.clear()
                break
            
            is_paused = self._pause.wait(0)
            while is_paused:
                is_paused = self._pause.wait(0)
            
    def pause(self):
        if self._pause.isSet():
            self._pause.clear()
            self.but_pau.config(text="Pause")
        
        elif not self._pause.isSet():
            self._pause.set()
            self.but_pau.config(text="Resume")
            
    def stop(self):
        self._kill.set()
        
    def destroy(self):
        self._kill.set()
        while self._kill.clear():
            pass
        self.timer_kill.set()
        while self.timer_kill.clear():
            pass
        self.clock_kill.set()
        while self.clock_kill.clear():
            pass
        self.runwindow.destroy()
        
    def add_device(self,device):
        self.totaldevices.append(device)
        val=device.returndevice()
        
        val_=[]
        for item in val:
            val_.append(item)
            
        for item in val_:
            if item[1]=='w':
                self.mem.subscribe_to_write(item[0],item[2])
            if item[1]=='w*':
                self.mem.subscribe_to_write(item[0],item[2])
            if item[1]=='r':
                self.mem.subscribe_to_read(item[0],item[2])
                
            if item[1]=='rw' or item[1]=='wr':
                self.mem.subscribe_to_read(item[0],item[2])
                self.mem.subscribe_to_write(item[0],item[2])
            
                
    def display_state(self):
        if self._pause.isSet():
            messagebox.showinfo("CPU State",self.result)
            
    def starttask(self):
        if not self._kill.isSet():
            Thread(target=self.runcpu).start()

            
    def memreset(self):
        for n in range(len(self.mem)):
            for key in list(self.specialwrites.keys()):
                if n in self.specialwrites[key]:
                    self.mem[n]=random.randint(0,255)+0x10000
                    continue
            self.mem[n]=random.randint(0,255)   
            
    def singlestep(self):
        self._pause.set()
        self.but_pau.config(text="Resume")
        
        result=cpu.step()
        self.result=result
        if result==None:
            messagebox.showinfo("Execution","Execution finished")
            
    def handler(self, event):
        value=event.char
        try:
            self.text.append(ord(value))
        except TypeError:
            pass
        
    def clockhandler(self):
        interval=1/self.clock_interval
        while True:
            time.sleep(interval)
            for item in self.clockhandlers:
                item()
                
            is_killed = self.clock_kill.wait(0)
            if is_killed:
                self.clock_kill.clear()
                break
                
        
        
    def start(self, frame_run, frame_txtout):      
        but_run=Button(frame_run,text="Run",command=self.starttask)
        but_run.grid(row=0,column=0,pady=5,padx=5,sticky="w")
        
        self.but_step=Button(frame_run,text="Step",command=self.singlestep)
        self.but_step.grid(row=0,column=1,pady=5,padx=5,sticky="w")
        
        self.but_pau=Button(frame_run,text="Pause",command=self.pause)
        self.but_pau.grid(row=0,column=2,pady=5,padx=5,sticky="w")
        
        self.but_stp=Button(frame_run,text="Stop",command=self.stop)
        self.but_stp.grid(row=0,column=3,pady=5,padx=5,sticky="w")

        but_state=Button(frame_run,text="CPU state",command=self.display_state)
        but_state.grid(row=0,column=4,pady=5,padx=5,sticky="w")
        
        but_reset=Button(frame_run,text="Reset",command=lambda: cpu.reset())
        but_reset.grid(row=0,column=5,pady=5,padx=5,sticky="w")
        
        but_meminit=Button(frame_run,text="Reset Memory",command=self.memreset)
        but_meminit.grid(row=0,column=6,pady=5,padx=5,sticky="w")
        
        
        labout=Label(frame_txtout, text="Input/Output") 
        labout.grid(row=0,column=0,pady=2,padx=2,sticky="w") 

        self.txtout=tkinter.scrolledtext.ScrolledText(frame_txtout, bg="white", width = 40, height = 10, )
        self.txtout.grid(row=1,column=0,pady=2,padx=2,sticky="w")  
        
        self.txtout.focus()
        self.txtout.configure(state ='disabled')
        self.txtout.bind_all("<KeyPress>", self.handler)
        
        self.but_cls=Button(frame_txtout, text="Clear",command=self.cleartxtout)
        self.but_cls.grid(row=3,column=0,pady=5,padx=5,sticky="w")
        
        
        self.txtout.delete('1.0', END)
        
        return frame_run, frame_txtout
        
    def cleartxtout(self):
        self.txtout.configure(state ='normal')
        self.txtout.delete("1.0","end")
        self.txtout.configure(state ='disabled')

class _dialog(tk.simpledialog.Dialog):
    def __init__(self, parent, title, value):
        self.value=value
        super().__init__(parent, title)

    def body(self, frame): 
        self.txtout=tkinter.scrolledtext.ScrolledText(frame, bg="white", width = 80, height = 10, )
        self.txtout.pack()
        
        self.txtout.focus()
        
        self.txtout.configure(state ='normal')
        self.txtout.delete("1.0","end")
        self.txtout.insert(tk.INSERT,self.value)
        self.txtout.configure(state ='disabled')

        return frame

    def cancel_pressed(self):
        self.destroy()
        
    def buttonbox(self):
        but_kill=Button(self,text="Close",command=self.cancel_pressed)
        but_kill.pack() 
        self.bind("<Return>", lambda event: self.cancel_pressed())
    
class infodisplay:
    def __init__(self):
        pass


    def setval(self, value):
        app=tk.Tk()
        app.withdraw()
        app.resizable(width=False, height=False)
        app.iconphoto(False, PhotoImage(master=app, file = 'res/65c02.png'))
        dialog=_dialog(title="Assembly",parent=app,value=value)
        
class devicewindow:
    def __init__(self,run):
        self.run=run
        
    def parseconfigs(self, devices):
        output_={}
        for device in devices:
            output_[device.name()]=[]
        for device in devices:
            output_[device.name()].append(device.returndevice())
        
        output=""
        for key in list(output_.keys()):
            output+=key+" - "
            for item in output_[key][0]:
                if min(item[0])==max(item[0]):
                    output+=str(hex(item[0][0]))+"   Mode: "+item[1]+"\n"+" "*len(key+" - ")
                else:
                    output+=str(hex(min(item[0])))+" - "+str(hex(max(item[0])))+"   Mode: "+item[1]+"\n"+" "*len(key+" - ")
            
            output+="\n"
            
        return output
            
        
    def start(self, frame):
        self.txtout=tkinter.scrolledtext.ScrolledText(frame, bg="white", width = 40, height = 10)
        self.txtout.grid(row=0,column=0,pady=10,padx=10)

        self.txtout.focus()
        
        self.txtout.configure(state ='normal')
        self.txtout.delete("1.0","end")
        self.txtout.insert(tk.INSERT,self.parseconfigs(self.run.totaldevices))
        self.txtout.configure(state ='disabled')

        return frame
        
class help_dialog(tk.simpledialog.Dialog):
    def __init__(self, parent, title, value):
        self.value=value
        super().__init__(parent, title)

    def body(self, frame): 
        self.txtout=tkinter.scrolledtext.ScrolledText(frame, bg="white", width = 40, height = 40, )
        self.txtout.pack()
        
        self.txtout.focus()
        
        self.txtout.configure(state ='normal')
        self.txtout.delete("1.0","end")
        self.txtout.insert(tk.INSERT,self.value)
        self.txtout.configure(state ='disabled')

        return frame

    def cancel_pressed(self):
        self.destroy()
        
    def buttonbox(self):
        but_kill=Button(self,text="Close",command=self.cancel_pressed)
        but_kill.pack() 
        self.bind("<Return>", lambda event: self.cancel_pressed())
    
class helpwindow:
    def __init__(self):
        pass
        
    def start(self):
        self.window = tkinter.Tk()
        self.window.title("Editor")
        self.window.minsize(200,50)
        self.window.resizable(width=False, height=False)
        self.window.iconphoto(False, PhotoImage(master=self.window, file = 'res/65c02.png'))
        

        btn_gettingstarted=tkinter.Button(self.window, text="Getting started", relief="raised", command=self.gettingstarted)
        btn_gettingstarted.grid(row=0,column=1,pady=2,padx=2,sticky="w")
        
        btn_basics=tkinter.Button(self.window,  text="65C02 Basics", relief="raised", command=self.basics)
        btn_basics.grid(row=0,column=0,pady=2,padx=2,sticky="w")
        
        btn_keybinds=tkinter.Button(self.window, text="Key binds", relief="raised", command=self.keybinds)
        btn_keybinds.grid(row=0,column=2,pady=2,padx=2,sticky="w")

        self.window.protocol("WM_DELETE_WINDOW",lambda: self.window.destroy())

        self.window.mainloop()
        
    def keybinds(self):
        text="""
        Ctrl+S - Save
        Ctrl+Shift+S - Save as
        Ctrl+O - Open assembly file
        Ctrl+B - Assemble
        Ctrl+Shift+O - Open binary file
        Ctrl+N - New window
        """
        
        messagebox.showinfo("Key bindings",text)
        
        
    def basics(self):
        text="""
        The 65C02 is a simple microprocessor. It has several
        builtin memory locations called "registers". Registers
        include A,X, and Y. The 65C02 can access 64kB of memory,
        or 65536 bytes of memory. The address range is hex 0
        to hex FFFF. The 65C02 uses a read-operate-write 
        architecture, which means that to preform operations,
        the 65C02 must load a value from memory into a register,
        do the operation and write the value back.
        
        Online, there are many resources to find the assembly
        code instructions to program the 65C02. To get
        started, click the "Getting started" button in the
        help window.
        """
        
        messagebox.showinfo("65C02 Basics",text)
        
        
    def gettingstarted(self):
        text="""
        To get started, open the editor. Inside, type these lines:
            
            .org $8000
        reset:
            lda #0
        loop:
            inc
            sta $7000
            bra loop
            
            .org $fffc
            .word reset
            
        What does this code do? 
        
        Line 1 (.org $8000) tells the emulator
        to start this code segment at the address $8000, which is
        hexadecimal for the number 32768. 
        
        Line 2 (reset:) tells the emulator to define a point in the
        code called reset.      
        
        Line 3 (lda #0) loads the the A register with the value 0.
                
        Line 4 (loop:) tells the emulator to define a point in the 
        code called loop.
        
        Line 5 (inc) adds 1 to the A register.
        
        Line 6 (sta $7000) outputs the value of the A register to 
        the console. 
        
        Line 7 (bra loop) preforms a quick jump to the "loop" 
        label.
        
        Line 8 (.org $fffc) tells the emulator to start this code 
        segment at the address $fffc.
        
        Line 9 (.word reset) puts the value of the address for
        reset at the next address after $fffc.
        
        
        To proceed, save this file and then click the "Assemble" 
        button. This will assemble the program and prepare it for
        execution
        
        Next, open the run winow. Click "Run". What do you see?
        """
        
        messagebox.showinfo("Getting started",text)
        
devices_name=[]

loaddevices="""
devices={}
ignore=[]
if os.path.isdir("devices"):
    for filename in os.listdir("devices"):
        if filename.endswith(".py"):
            with open("devices/"+filename, "r") as file:
                startlocals=list(locals().keys())
                exec(file.read(),globals(),locals())
                endlocals=list(locals().keys())
                file_=None
                filename_=filename.split(".")[0]
                for item in endlocals:
                    if item not in startlocals and item!="startlocals":
                        try:
                            if item=='num_'+file_:
                                if 'num_'+file_ not in devices_name:
                                    devices_name.append('num_'+file_)
                                num=locals()[item]
                                devices[file_].append(num)
                                continue
                            if item=='base_'+file_:
                                if 'base_'+file_ not in devices_name:
                                    devices_name.append('base_'+file_)
                                base=locals()[item]
                                devices[file_].append(base)
                                continue
                            
                            if item=='IGNORE':
                                for item_ in locals()[item]:
                                    ignore.append(item_)
                                continue
                        except TypeError:
                            pass
                        file_=item
                        if item not in devices_name:
                            devices_name.append(item)
                        devices[item]=[]
                        
                        
devicenames=[]
for key in list(devices.keys()):
    if key in ignore:
        continue
    for n in range(devices[key][0]):
        startlocals=list(locals().keys())
        exec(key+str(n)+"="+key+"("+str(n)+", "+str(devices[key][1][n])+", run)")
        endlocals=list(locals().keys())
        
        for item in endlocals:
            if item not in startlocals and item!="startlocals":
                devicenames.append(item)


for key in devicenames:
    exec("run.add_device("+key+")")
    
specialwrites={}
for item_ in devicenames:
    startlocals=list(locals().keys())
    exec("dev="+item_+".returndevice()")
    endlocals=list(locals().keys())
    
    for item in endlocals:
        if item not in startlocals and item!="startlocals":
            dev=locals()[item]
    
    for item in dev:
        if item[1]=="w*":
            specialwrites[item_]=item[0]
            
print("Devices loaded.")
                
"""

files=loadfiles(mem)

dump=dumpmem(mem) 
dismbl=disassmbl(mem)   
edit=editmem(mem)  
read=readbyte(mem)

infowin=infodisplay()
editorwin=editor(mem,infowin,files)

run=runclass(cpu,mem)
 
devwin=devicewindow(run)
helpwin=helpwindow()

exec(loaddevices,globals(),locals())   


#for n in tqdm.tqdm(range(len(mem))):
#    for key in list(specialwrites.keys()):
#        if n in specialwrites[key]:
#            mem[n]=random.randint(0,255)+0x10000
#            continue
#    mem[n]=random.randint(0,255)

run.specialwrites=specialwrites

window = tkinter.Tk()
window.title("65C02 Emulator")

window.iconphoto(False, PhotoImage(master=window, file = 'res/65c02.png'))

row1=Frame(window)
row1.grid(row=0,column=0,pady=5,padx=5,sticky="nw")

lab_dump=Label(row1, text='Dump memory', font='Helvetica 10 bold')
lab_dump.grid(row=0,column=0,pady=5,padx=5)
#Dump
dumpframe=Frame(row1)
dumpframe.grid(row=1,column=0,pady=5,padx=5,sticky="wn")
dump.start(dumpframe)

lab_dismbl=Label(row1, text='Disassemble memory', font='Helvetica 10 bold')
lab_dismbl.grid(row=0,column=1,pady=5,padx=5)
#Dismbl
dismblframe=Frame(row1)
dismblframe.grid(row=1,column=1,pady=5,padx=5,sticky="w")
dismbl.start(dismblframe)

row2=Frame(window)
row2.grid(row=0,column=1,pady=5,padx=5,sticky="nw")

lab_edit=Label(row2, text='Edit byte', font='Helvetica 10 bold')
lab_edit.grid(row=0,column=2,pady=5,padx=5)
#edit
editframe=Frame(row2)
editframe.grid(row=1,column=2,pady=5,padx=5,sticky="wn")
edit.start(editframe)

spacer=Label(row2)
spacer.grid(row=0,column=3,pady=0,padx=10)

lab_read=Label(row2, text='Read byte', font='Helvetica 10 bold')
lab_read.grid(row=0,column=4,pady=5,padx=5)
#Read
readframe=Frame(row2)
readframe.grid(row=1,column=4,pady=5,padx=5,sticky="wn")
read.start(readframe)

spacer2=Label(row2)
spacer2.grid(row=0,column=5,pady=0,padx=50)
#HELP
btn_help=tkinter.Button(row2,  text="Help", relief="raised", command=helpwin.start)
btn_help.grid(row=0,column=6,pady=2,padx=2,sticky="e")


row3=Frame(window)
row3.grid(row=1,column=0,pady=5,padx=5,sticky="nw")


lab_editor=Label(row3, text='Editor', font='Helvetica 10 bold')
lab_editor.grid(row=0,column=0,pady=5,padx=5,sticky="wn")
#editorwin
editorwin_buttonframe=Frame(row3)
editorwin_buttonframe.grid(row=1,column=0,pady=5,padx=5,sticky="wn")
editorwin_texteditframe=Frame(row3)
editorwin_texteditframe.grid(row=2,column=0,pady=5,padx=5,sticky="wn")
files.start(editorwin_buttonframe)
editorwin.start(editorwin_buttonframe,editorwin_texteditframe)


row4=Frame(window)
row4.grid(row=1,column=1,pady=5,padx=5,sticky="nw")

lab_run=Label(row4, text='Run', font='Helvetica 10 bold')
lab_run.grid(row=0,column=0,pady=5,padx=5,sticky="wn")

#Run
runframe_buttons=Frame(row4)
runframe_buttons.grid(row=1,column=0,pady=5,padx=5,sticky="wn")

runframe_txtout=Frame(row4)
runframe_txtout.grid(row=2,column=0,pady=5,padx=5,sticky="wn")

run.start(runframe_buttons,runframe_txtout)

lab_dev=Label(row4, text='Devices', font='Helvetica 10 bold')
lab_dev.grid(row=3,column=0,pady=5,padx=5,sticky="wn")
#Device window
devframe=Frame(row4)
devframe.grid(row=4,column=0,pady=5,padx=5,sticky="wn")

devwin.start(devframe)


window.bind("<Control-Shift-S>", editorwin.saveas)
window.bind("<Control-s>", editorwin.savecurrent)
window.bind("<Control-o>", editorwin.openfile)
window.bind("<Control-b>", editorwin.quickasm)
window.bind("<Control-Shift-O>", files._start)
window.bind("<Control-n>", editorwin.newwin)
window.mainloop()    
    
    
