/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   sat_cutset_compute_shift.h

  Author:

    Nikolaj Bjorner 2020-01-02

  Notes:
    
    shifts truth table x using 'code'.
    code encodes a mapping from bit-positions of the 
    input truth table encoded with x into bit-positions
    in the output truth table.
    The truth table covers up to 6 inputs, which fits in 64 bits.

  --*/

static uint64_t compute_shift(uint64_t x, unsigned code) {
    switch (code) {
#define _x0 (x & 1)
#define _x1 _x0
    case 1: return _x1;
#define _x2 (_x1 | (_x1 << 1))
    case 2: return _x2;
#define _x3 (x & 3)
#define _x4 _x3
    case 3: return _x4;
#define _x5 (_x2 | (_x2 << 2))
    case 4: return _x5;
#define _x6 (_x4 | (_x4 << 2))
    case 5: return _x6;
#define _x7 (x & 2)
#define _x8 (_x7 << 1)
#define _x9 (_x8 | (_x8 << 1))
#define _x10 (_x2 | _x9)
    case 6: return _x10;
#define _x11 (x & 15)
#define _x12 _x11
    case 7: return _x12;
#define _x13 (_x5 | (_x5 << 4))
    case 8: return _x13;
#define _x14 (_x6 | (_x6 << 4))
    case 9: return _x14;
#define _x15 (_x10 | (_x10 << 4))
    case 10: return _x15;
#define _x16 (_x12 | (_x12 << 4))
    case 11: return _x16;
#define _x17 (_x7 << 3)
#define _x18 (_x17 | (_x17 << 1))
#define _x19 (_x18 | (_x18 << 2))
#define _x20 (_x5 | _x19)
    case 12: return _x20;
#define _x21 (x & 12)
#define _x22 (_x21 << 2)
#define _x23 (_x22 | (_x22 << 2))
#define _x24 (_x6 | _x23)
    case 13: return _x24;
#define _x25 (x & 4)
#define _x26 (_x25 << 2)
#define _x27 (_x26 | (_x26 << 1))
#define _x28 (x & 8)
#define _x29 (_x28 << 3)
#define _x30 (_x29 | (_x29 << 1))
#define _x31 (_x27 | _x30)
#define _x32 (_x10 | _x31)
    case 14: return _x32;
#define _x33 (x & 255)
#define _x34 _x33
    case 15: return _x34;
#define _x35 (_x13 | (_x13 << 8))
    case 16: return _x35;
#define _x36 (_x14 | (_x14 << 8))
    case 17: return _x36;
#define _x37 (_x15 | (_x15 << 8))
    case 18: return _x37;
#define _x38 (_x16 | (_x16 << 8))
    case 19: return _x38;
#define _x39 (_x20 | (_x20 << 8))
    case 20: return _x39;
#define _x40 (_x24 | (_x24 << 8))
    case 21: return _x40;
#define _x41 (_x32 | (_x32 << 8))
    case 22: return _x41;
#define _x42 (_x34 | (_x34 << 8))
    case 23: return _x42;
#define _x43 (_x7 << 7)
#define _x44 (_x43 | (_x43 << 1))
#define _x45 (_x44 | (_x44 << 2))
#define _x46 (_x45 | (_x45 << 4))
#define _x47 (_x13 | _x46)
    case 24: return _x47;
#define _x48 (_x21 << 6)
#define _x49 (_x48 | (_x48 << 2))
#define _x50 (_x49 | (_x49 << 4))
#define _x51 (_x14 | _x50)
    case 25: return _x51;
#define _x52 (_x25 << 6)
#define _x53 (_x52 | (_x52 << 1))
#define _x54 (_x28 << 7)
#define _x55 (_x54 | (_x54 << 1))
#define _x56 (_x53 | _x55)
#define _x57 (_x56 | (_x56 << 4))
#define _x58 (_x15 | _x57)
    case 26: return _x58;
#define _x59 (x & 240)
#define _x60 (_x59 << 4)
#define _x61 (_x60 | (_x60 << 4))
#define _x62 (_x16 | _x61)
    case 27: return _x62;
#define _x63 (_x53 | (_x53 << 2))
#define _x64 (_x28 << 9)
#define _x65 (_x64 | (_x64 << 1))
#define _x66 (_x65 | (_x65 << 2))
#define _x67 (_x63 | _x66)
#define _x68 (_x20 | _x67)
    case 28: return _x68;
#define _x69 (x & 48)
#define _x70 (_x69 << 4)
#define _x71 (_x70 | (_x70 << 2))
#define _x72 (x & 192)
#define _x73 (_x72 << 6)
#define _x74 (_x73 | (_x73 << 2))
#define _x75 (_x71 | _x74)
#define _x76 (_x24 | _x75)
    case 29: return _x76;
#define _x77 (x & 16)
#define _x78 (_x77 << 4)
#define _x79 (_x78 | (_x78 << 1))
#define _x80 (x & 32)
#define _x81 (_x80 << 5)
#define _x82 (_x81 | (_x81 << 1))
#define _x83 (_x79 | _x82)
#define _x84 (x & 64)
#define _x85 (_x84 << 6)
#define _x86 (_x85 | (_x85 << 1))
#define _x87 (x & 128)
#define _x88 (_x87 << 7)
#define _x89 (_x88 | (_x88 << 1))
#define _x90 (_x86 | _x89)
#define _x91 (_x83 | _x90)
#define _x92 (_x32 | _x91)
    case 30: return _x92;
#define _x93 (x & 65535)
#define _x94 _x93
    case 31: return _x94;
#define _x95 (_x35 | (_x35 << 16))
    case 32: return _x95;
#define _x96 (_x36 | (_x36 << 16))
    case 33: return _x96;
#define _x97 (_x37 | (_x37 << 16))
    case 34: return _x97;
#define _x98 (_x38 | (_x38 << 16))
    case 35: return _x98;
#define _x99 (_x39 | (_x39 << 16))
    case 36: return _x99;
#define _x100 (_x40 | (_x40 << 16))
    case 37: return _x100;
#define _x101 (_x41 | (_x41 << 16))
    case 38: return _x101;
#define _x102 (_x42 | (_x42 << 16))
    case 39: return _x102;
#define _x103 (_x47 | (_x47 << 16))
    case 40: return _x103;
#define _x104 (_x51 | (_x51 << 16))
    case 41: return _x104;
#define _x105 (_x58 | (_x58 << 16))
    case 42: return _x105;
#define _x106 (_x62 | (_x62 << 16))
    case 43: return _x106;
#define _x107 (_x68 | (_x68 << 16))
    case 44: return _x107;
#define _x108 (_x76 | (_x76 << 16))
    case 45: return _x108;
#define _x109 (_x92 | (_x92 << 16))
    case 46: return _x109;
#define _x110 (_x94 | (_x94 << 16))
    case 47: return _x110;
#define _x111 (_x7 << 15)
#define _x112 (_x111 | (_x111 << 1))
#define _x113 (_x112 | (_x112 << 2))
#define _x114 (_x113 | (_x113 << 4))
#define _x115 (_x114 | (_x114 << 8))
#define _x116 (_x35 | _x115)
    case 48: return _x116;
#define _x117 (_x21 << 14)
#define _x118 (_x117 | (_x117 << 2))
#define _x119 (_x118 | (_x118 << 4))
#define _x120 (_x119 | (_x119 << 8))
#define _x121 (_x36 | _x120)
    case 49: return _x121;
#define _x122 (_x25 << 14)
#define _x123 (_x122 | (_x122 << 1))
#define _x124 (_x28 << 15)
#define _x125 (_x124 | (_x124 << 1))
#define _x126 (_x123 | _x125)
#define _x127 (_x126 | (_x126 << 4))
#define _x128 (_x127 | (_x127 << 8))
#define _x129 (_x37 | _x128)
    case 50: return _x129;
#define _x130 (_x59 << 12)
#define _x131 (_x130 | (_x130 << 4))
#define _x132 (_x131 | (_x131 << 8))
#define _x133 (_x38 | _x132)
    case 51: return _x133;
#define _x134 (_x123 | (_x123 << 2))
#define _x135 (_x28 << 17)
#define _x136 (_x135 | (_x135 << 1))
#define _x137 (_x136 | (_x136 << 2))
#define _x138 (_x134 | _x137)
#define _x139 (_x138 | (_x138 << 8))
#define _x140 (_x39 | _x139)
    case 52: return _x140;
#define _x141 (_x69 << 12)
#define _x142 (_x141 | (_x141 << 2))
#define _x143 (_x72 << 14)
#define _x144 (_x143 | (_x143 << 2))
#define _x145 (_x142 | _x144)
#define _x146 (_x145 | (_x145 << 8))
#define _x147 (_x40 | _x146)
    case 53: return _x147;
#define _x148 (_x77 << 12)
#define _x149 (_x148 | (_x148 << 1))
#define _x150 (_x80 << 13)
#define _x151 (_x150 | (_x150 << 1))
#define _x152 (_x149 | _x151)
#define _x153 (_x84 << 14)
#define _x154 (_x153 | (_x153 << 1))
#define _x155 (_x87 << 15)
#define _x156 (_x155 | (_x155 << 1))
#define _x157 (_x154 | _x156)
#define _x158 (_x152 | _x157)
#define _x159 (_x158 | (_x158 << 8))
#define _x160 (_x41 | _x159)
    case 54: return _x160;
#define _x161 (x & 65280)
#define _x162 (_x161 << 8)
#define _x163 (_x162 | (_x162 << 8))
#define _x164 (_x42 | _x163)
    case 55: return _x164;
#define _x165 (_x134 | (_x134 << 4))
#define _x166 (_x28 << 21)
#define _x167 (_x166 | (_x166 << 1))
#define _x168 (_x167 | (_x167 << 2))
#define _x169 (_x168 | (_x168 << 4))
#define _x170 (_x165 | _x169)
#define _x171 (_x47 | _x170)
    case 56: return _x171;
#define _x172 (_x142 | (_x142 << 4))
#define _x173 (_x72 << 18)
#define _x174 (_x173 | (_x173 << 2))
#define _x175 (_x174 | (_x174 << 4))
#define _x176 (_x172 | _x175)
#define _x177 (_x51 | _x176)
    case 57: return _x177;
#define _x178 (_x152 | (_x152 << 4))
#define _x179 (_x84 << 18)
#define _x180 (_x179 | (_x179 << 1))
#define _x181 (_x87 << 19)
#define _x182 (_x181 | (_x181 << 1))
#define _x183 (_x180 | _x182)
#define _x184 (_x183 | (_x183 << 4))
#define _x185 (_x178 | _x184)
#define _x186 (_x58 | _x185)
    case 58: return _x186;
#define _x187 (x & 3840)
#define _x188 (_x187 << 8)
#define _x189 (_x188 | (_x188 << 4))
#define _x190 (x & 61440)
#define _x191 (_x190 << 12)
#define _x192 (_x191 | (_x191 << 4))
#define _x193 (_x189 | _x192)
#define _x194 (_x62 | _x193)
    case 59: return _x194;
#define _x195 (_x149 | (_x149 << 2))
#define _x196 (_x80 << 15)
#define _x197 (_x196 | (_x196 << 1))
#define _x198 (_x197 | (_x197 << 2))
#define _x199 (_x195 | _x198)
#define _x200 (_x180 | (_x180 << 2))
#define _x201 (_x87 << 21)
#define _x202 (_x201 | (_x201 << 1))
#define _x203 (_x202 | (_x202 << 2))
#define _x204 (_x200 | _x203)
#define _x205 (_x199 | _x204)
#define _x206 (_x68 | _x205)
    case 60: return _x206;
#define _x207 (x & 768)
#define _x208 (_x207 << 8)
#define _x209 (_x208 | (_x208 << 2))
#define _x210 (x & 3072)
#define _x211 (_x210 << 10)
#define _x212 (_x211 | (_x211 << 2))
#define _x213 (_x209 | _x212)
#define _x214 (x & 12288)
#define _x215 (_x214 << 12)
#define _x216 (_x215 | (_x215 << 2))
#define _x217 (x & 49152)
#define _x218 (_x217 << 14)
#define _x219 (_x218 | (_x218 << 2))
#define _x220 (_x216 | _x219)
#define _x221 (_x213 | _x220)
#define _x222 (_x76 | _x221)
    case 61: return _x222;
#define _x223 (x & 256)
#define _x224 (_x223 << 8)
#define _x225 (_x224 | (_x224 << 1))
#define _x226 (x & 512)
#define _x227 (_x226 << 9)
#define _x228 (_x227 | (_x227 << 1))
#define _x229 (_x225 | _x228)
#define _x230 (x & 1024)
#define _x231 (_x230 << 10)
#define _x232 (_x231 | (_x231 << 1))
#define _x233 (x & 2048)
#define _x234 (_x233 << 11)
#define _x235 (_x234 | (_x234 << 1))
#define _x236 (_x232 | _x235)
#define _x237 (_x229 | _x236)
#define _x238 (x & 4096)
#define _x239 (_x238 << 12)
#define _x240 (_x239 | (_x239 << 1))
#define _x241 (x & 8192)
#define _x242 (_x241 << 13)
#define _x243 (_x242 | (_x242 << 1))
#define _x244 (_x240 | _x243)
#define _x245 (x & 16384)
#define _x246 (_x245 << 14)
#define _x247 (_x246 | (_x246 << 1))
#define _x248 (x & 32768)
#define _x249 (_x248 << 15)
#define _x250 (_x249 | (_x249 << 1))
#define _x251 (_x247 | _x250)
#define _x252 (_x244 | _x251)
#define _x253 (_x237 | _x252)
#define _x254 (_x92 | _x253)
    case 62: return _x254;
#define _x255 (x & 4294967295)
#define _x256 _x255
    case 63: return _x256;
#define _x257 (_x95 | (_x95 << 32))
    case 64: return _x257;
#define _x258 (_x96 | (_x96 << 32))
    case 65: return _x258;
#define _x259 (_x97 | (_x97 << 32))
    case 66: return _x259;
#define _x260 (_x98 | (_x98 << 32))
    case 67: return _x260;
#define _x261 (_x99 | (_x99 << 32))
    case 68: return _x261;
#define _x262 (_x100 | (_x100 << 32))
    case 69: return _x262;
#define _x263 (_x101 | (_x101 << 32))
    case 70: return _x263;
#define _x264 (_x102 | (_x102 << 32))
    case 71: return _x264;
#define _x265 (_x103 | (_x103 << 32))
    case 72: return _x265;
#define _x266 (_x104 | (_x104 << 32))
    case 73: return _x266;
#define _x267 (_x105 | (_x105 << 32))
    case 74: return _x267;
#define _x268 (_x106 | (_x106 << 32))
    case 75: return _x268;
#define _x269 (_x107 | (_x107 << 32))
    case 76: return _x269;
#define _x270 (_x108 | (_x108 << 32))
    case 77: return _x270;
#define _x271 (_x109 | (_x109 << 32))
    case 78: return _x271;
#define _x272 (_x110 | (_x110 << 32))
    case 79: return _x272;
#define _x273 (_x116 | (_x116 << 32))
    case 80: return _x273;
#define _x274 (_x121 | (_x121 << 32))
    case 81: return _x274;
#define _x275 (_x129 | (_x129 << 32))
    case 82: return _x275;
#define _x276 (_x133 | (_x133 << 32))
    case 83: return _x276;
#define _x277 (_x140 | (_x140 << 32))
    case 84: return _x277;
#define _x278 (_x147 | (_x147 << 32))
    case 85: return _x278;
#define _x279 (_x160 | (_x160 << 32))
    case 86: return _x279;
#define _x280 (_x164 | (_x164 << 32))
    case 87: return _x280;
#define _x281 (_x171 | (_x171 << 32))
    case 88: return _x281;
#define _x282 (_x177 | (_x177 << 32))
    case 89: return _x282;
#define _x283 (_x186 | (_x186 << 32))
    case 90: return _x283;
#define _x284 (_x194 | (_x194 << 32))
    case 91: return _x284;
#define _x285 (_x206 | (_x206 << 32))
    case 92: return _x285;
#define _x286 (_x222 | (_x222 << 32))
    case 93: return _x286;
#define _x287 (_x254 | (_x254 << 32))
    case 94: return _x287;
#define _x288 (_x256 | (_x256 << 32))
    case 95: return _x288;
#define _x289 (_x7 << 31)
#define _x290 (_x289 | (_x289 << 1))
#define _x291 (_x290 | (_x290 << 2))
#define _x292 (_x291 | (_x291 << 4))
#define _x293 (_x292 | (_x292 << 8))
#define _x294 (_x293 | (_x293 << 16))
#define _x295 (_x95 | _x294)
    case 96: return _x295;
#define _x296 (_x21 << 30)
#define _x297 (_x296 | (_x296 << 2))
#define _x298 (_x297 | (_x297 << 4))
#define _x299 (_x298 | (_x298 << 8))
#define _x300 (_x299 | (_x299 << 16))
#define _x301 (_x96 | _x300)
    case 97: return _x301;
#define _x302 (_x25 << 30)
#define _x303 (_x302 | (_x302 << 1))
#define _x304 (_x28 << 31)
#define _x305 (_x304 | (_x304 << 1))
#define _x306 (_x303 | _x305)
#define _x307 (_x306 | (_x306 << 4))
#define _x308 (_x307 | (_x307 << 8))
#define _x309 (_x308 | (_x308 << 16))
#define _x310 (_x97 | _x309)
    case 98: return _x310;
#define _x311 (_x59 << 28)
#define _x312 (_x311 | (_x311 << 4))
#define _x313 (_x312 | (_x312 << 8))
#define _x314 (_x313 | (_x313 << 16))
#define _x315 (_x98 | _x314)
    case 99: return _x315;
#define _x316 (_x303 | (_x303 << 2))
#define _x317 (_x28 << 33)
#define _x318 (_x317 | (_x317 << 1))
#define _x319 (_x318 | (_x318 << 2))
#define _x320 (_x316 | _x319)
#define _x321 (_x320 | (_x320 << 8))
#define _x322 (_x321 | (_x321 << 16))
#define _x323 (_x99 | _x322)
    case 100: return _x323;
#define _x324 (_x69 << 28)
#define _x325 (_x324 | (_x324 << 2))
#define _x326 (_x72 << 30)
#define _x327 (_x326 | (_x326 << 2))
#define _x328 (_x325 | _x327)
#define _x329 (_x328 | (_x328 << 8))
#define _x330 (_x329 | (_x329 << 16))
#define _x331 (_x100 | _x330)
    case 101: return _x331;
#define _x332 (_x77 << 28)
#define _x333 (_x332 | (_x332 << 1))
#define _x334 (_x80 << 29)
#define _x335 (_x334 | (_x334 << 1))
#define _x336 (_x333 | _x335)
#define _x337 (_x84 << 30)
#define _x338 (_x337 | (_x337 << 1))
#define _x339 (_x87 << 31)
#define _x340 (_x339 | (_x339 << 1))
#define _x341 (_x338 | _x340)
#define _x342 (_x336 | _x341)
#define _x343 (_x342 | (_x342 << 8))
#define _x344 (_x343 | (_x343 << 16))
#define _x345 (_x101 | _x344)
    case 102: return _x345;
#define _x346 (_x161 << 24)
#define _x347 (_x346 | (_x346 << 8))
#define _x348 (_x347 | (_x347 << 16))
#define _x349 (_x102 | _x348)
    case 103: return _x349;
#define _x350 (_x316 | (_x316 << 4))
#define _x351 (_x28 << 37)
#define _x352 (_x351 | (_x351 << 1))
#define _x353 (_x352 | (_x352 << 2))
#define _x354 (_x353 | (_x353 << 4))
#define _x355 (_x350 | _x354)
#define _x356 (_x355 | (_x355 << 16))
#define _x357 (_x103 | _x356)
    case 104: return _x357;
#define _x358 (_x325 | (_x325 << 4))
#define _x359 (_x72 << 34)
#define _x360 (_x359 | (_x359 << 2))
#define _x361 (_x360 | (_x360 << 4))
#define _x362 (_x358 | _x361)
#define _x363 (_x362 | (_x362 << 16))
#define _x364 (_x104 | _x363)
    case 105: return _x364;
#define _x365 (_x336 | (_x336 << 4))
#define _x366 (_x84 << 34)
#define _x367 (_x366 | (_x366 << 1))
#define _x368 (_x87 << 35)
#define _x369 (_x368 | (_x368 << 1))
#define _x370 (_x367 | _x369)
#define _x371 (_x370 | (_x370 << 4))
#define _x372 (_x365 | _x371)
#define _x373 (_x372 | (_x372 << 16))
#define _x374 (_x105 | _x373)
    case 106: return _x374;
#define _x375 (_x187 << 24)
#define _x376 (_x375 | (_x375 << 4))
#define _x377 (_x190 << 28)
#define _x378 (_x377 | (_x377 << 4))
#define _x379 (_x376 | _x378)
#define _x380 (_x379 | (_x379 << 16))
#define _x381 (_x106 | _x380)
    case 107: return _x381;
#define _x382 (_x333 | (_x333 << 2))
#define _x383 (_x80 << 31)
#define _x384 (_x383 | (_x383 << 1))
#define _x385 (_x384 | (_x384 << 2))
#define _x386 (_x382 | _x385)
#define _x387 (_x367 | (_x367 << 2))
#define _x388 (_x87 << 37)
#define _x389 (_x388 | (_x388 << 1))
#define _x390 (_x389 | (_x389 << 2))
#define _x391 (_x387 | _x390)
#define _x392 (_x386 | _x391)
#define _x393 (_x392 | (_x392 << 16))
#define _x394 (_x107 | _x393)
    case 108: return _x394;
#define _x395 (_x207 << 24)
#define _x396 (_x395 | (_x395 << 2))
#define _x397 (_x210 << 26)
#define _x398 (_x397 | (_x397 << 2))
#define _x399 (_x396 | _x398)
#define _x400 (_x214 << 28)
#define _x401 (_x400 | (_x400 << 2))
#define _x402 (_x217 << 30)
#define _x403 (_x402 | (_x402 << 2))
#define _x404 (_x401 | _x403)
#define _x405 (_x399 | _x404)
#define _x406 (_x405 | (_x405 << 16))
#define _x407 (_x108 | _x406)
    case 109: return _x407;
#define _x408 (_x223 << 24)
#define _x409 (_x408 | (_x408 << 1))
#define _x410 (_x226 << 25)
#define _x411 (_x410 | (_x410 << 1))
#define _x412 (_x409 | _x411)
#define _x413 (_x230 << 26)
#define _x414 (_x413 | (_x413 << 1))
#define _x415 (_x233 << 27)
#define _x416 (_x415 | (_x415 << 1))
#define _x417 (_x414 | _x416)
#define _x418 (_x412 | _x417)
#define _x419 (_x238 << 28)
#define _x420 (_x419 | (_x419 << 1))
#define _x421 (_x241 << 29)
#define _x422 (_x421 | (_x421 << 1))
#define _x423 (_x420 | _x422)
#define _x424 (_x245 << 30)
#define _x425 (_x424 | (_x424 << 1))
#define _x426 (_x248 << 31)
#define _x427 (_x426 | (_x426 << 1))
#define _x428 (_x425 | _x427)
#define _x429 (_x423 | _x428)
#define _x430 (_x418 | _x429)
#define _x431 (_x430 | (_x430 << 16))
#define _x432 (_x109 | _x431)
    case 110: return _x432;
#define _x433 (x & 4294901760)
#define _x434 (_x433 << 16)
#define _x435 (_x434 | (_x434 << 16))
#define _x436 (_x110 | _x435)
    case 111: return _x436;
#define _x437 (_x350 | (_x350 << 8))
#define _x438 (_x28 << 45)
#define _x439 (_x438 | (_x438 << 1))
#define _x440 (_x439 | (_x439 << 2))
#define _x441 (_x440 | (_x440 << 4))
#define _x442 (_x441 | (_x441 << 8))
#define _x443 (_x437 | _x442)
#define _x444 (_x116 | _x443)
    case 112: return _x444;
#define _x445 (_x358 | (_x358 << 8))
#define _x446 (_x72 << 42)
#define _x447 (_x446 | (_x446 << 2))
#define _x448 (_x447 | (_x447 << 4))
#define _x449 (_x448 | (_x448 << 8))
#define _x450 (_x445 | _x449)
#define _x451 (_x121 | _x450)
    case 113: return _x451;
#define _x452 (_x365 | (_x365 << 8))
#define _x453 (_x84 << 42)
#define _x454 (_x453 | (_x453 << 1))
#define _x455 (_x87 << 43)
#define _x456 (_x455 | (_x455 << 1))
#define _x457 (_x454 | _x456)
#define _x458 (_x457 | (_x457 << 4))
#define _x459 (_x458 | (_x458 << 8))
#define _x460 (_x452 | _x459)
#define _x461 (_x129 | _x460)
    case 114: return _x461;
#define _x462 (_x376 | (_x376 << 8))
#define _x463 (_x190 << 36)
#define _x464 (_x463 | (_x463 << 4))
#define _x465 (_x464 | (_x464 << 8))
#define _x466 (_x462 | _x465)
#define _x467 (_x133 | _x466)
    case 115: return _x467;
#define _x468 (_x386 | (_x386 << 8))
#define _x469 (_x454 | (_x454 << 2))
#define _x470 (_x87 << 45)
#define _x471 (_x470 | (_x470 << 1))
#define _x472 (_x471 | (_x471 << 2))
#define _x473 (_x469 | _x472)
#define _x474 (_x473 | (_x473 << 8))
#define _x475 (_x468 | _x474)
#define _x476 (_x140 | _x475)
    case 116: return _x476;
#define _x477 (_x399 | (_x399 << 8))
#define _x478 (_x214 << 36)
#define _x479 (_x478 | (_x478 << 2))
#define _x480 (_x217 << 38)
#define _x481 (_x480 | (_x480 << 2))
#define _x482 (_x479 | _x481)
#define _x483 (_x482 | (_x482 << 8))
#define _x484 (_x477 | _x483)
#define _x485 (_x147 | _x484)
    case 117: return _x485;
#define _x486 (_x418 | (_x418 << 8))
#define _x487 (_x238 << 36)
#define _x488 (_x487 | (_x487 << 1))
#define _x489 (_x241 << 37)
#define _x490 (_x489 | (_x489 << 1))
#define _x491 (_x488 | _x490)
#define _x492 (_x245 << 38)
#define _x493 (_x492 | (_x492 << 1))
#define _x494 (_x248 << 39)
#define _x495 (_x494 | (_x494 << 1))
#define _x496 (_x493 | _x495)
#define _x497 (_x491 | _x496)
#define _x498 (_x497 | (_x497 << 8))
#define _x499 (_x486 | _x498)
#define _x500 (_x160 | _x499)
    case 118: return _x500;
#define _x501 (x & 16711680)
#define _x502 (_x501 << 16)
#define _x503 (_x502 | (_x502 << 8))
#define _x504 (x & 4278190080)
#define _x505 (_x504 << 24)
#define _x506 (_x505 | (_x505 << 8))
#define _x507 (_x503 | _x506)
#define _x508 (_x164 | _x507)
    case 119: return _x508;
#define _x509 (_x382 | (_x382 << 4))
#define _x510 (_x80 << 35)
#define _x511 (_x510 | (_x510 << 1))
#define _x512 (_x511 | (_x511 << 2))
#define _x513 (_x512 | (_x512 << 4))
#define _x514 (_x509 | _x513)
#define _x515 (_x469 | (_x469 << 4))
#define _x516 (_x87 << 49)
#define _x517 (_x516 | (_x516 << 1))
#define _x518 (_x517 | (_x517 << 2))
#define _x519 (_x518 | (_x518 << 4))
#define _x520 (_x515 | _x519)
#define _x521 (_x514 | _x520)
#define _x522 (_x171 | _x521)
    case 120: return _x522;
#define _x523 (_x396 | (_x396 << 4))
#define _x524 (_x210 << 30)
#define _x525 (_x524 | (_x524 << 2))
#define _x526 (_x525 | (_x525 << 4))
#define _x527 (_x523 | _x526)
#define _x528 (_x479 | (_x479 << 4))
#define _x529 (_x217 << 42)
#define _x530 (_x529 | (_x529 << 2))
#define _x531 (_x530 | (_x530 << 4))
#define _x532 (_x528 | _x531)
#define _x533 (_x527 | _x532)
#define _x534 (_x177 | _x533)
    case 121: return _x534;
#define _x535 (_x412 | (_x412 << 4))
#define _x536 (_x230 << 30)
#define _x537 (_x536 | (_x536 << 1))
#define _x538 (_x233 << 31)
#define _x539 (_x538 | (_x538 << 1))
#define _x540 (_x537 | _x539)
#define _x541 (_x540 | (_x540 << 4))
#define _x542 (_x535 | _x541)
#define _x543 (_x491 | (_x491 << 4))
#define _x544 (_x245 << 42)
#define _x545 (_x544 | (_x544 << 1))
#define _x546 (_x248 << 43)
#define _x547 (_x546 | (_x546 << 1))
#define _x548 (_x545 | _x547)
#define _x549 (_x548 | (_x548 << 4))
#define _x550 (_x543 | _x549)
#define _x551 (_x542 | _x550)
#define _x552 (_x186 | _x551)
    case 122: return _x552;
#define _x553 (x & 983040)
#define _x554 (_x553 << 16)
#define _x555 (_x554 | (_x554 << 4))
#define _x556 (x & 15728640)
#define _x557 (_x556 << 20)
#define _x558 (_x557 | (_x557 << 4))
#define _x559 (_x555 | _x558)
#define _x560 (x & 251658240)
#define _x561 (_x560 << 24)
#define _x562 (_x561 | (_x561 << 4))
#define _x563 (x & 4026531840)
#define _x564 (_x563 << 28)
#define _x565 (_x564 | (_x564 << 4))
#define _x566 (_x562 | _x565)
#define _x567 (_x559 | _x566)
#define _x568 (_x194 | _x567)
    case 123: return _x568;
#define _x569 (_x409 | (_x409 << 2))
#define _x570 (_x226 << 27)
#define _x571 (_x570 | (_x570 << 1))
#define _x572 (_x571 | (_x571 << 2))
#define _x573 (_x569 | _x572)
#define _x574 (_x537 | (_x537 << 2))
#define _x575 (_x233 << 33)
#define _x576 (_x575 | (_x575 << 1))
#define _x577 (_x576 | (_x576 << 2))
#define _x578 (_x574 | _x577)
#define _x579 (_x573 | _x578)
#define _x580 (_x488 | (_x488 << 2))
#define _x581 (_x241 << 39)
#define _x582 (_x581 | (_x581 << 1))
#define _x583 (_x582 | (_x582 << 2))
#define _x584 (_x580 | _x583)
#define _x585 (_x545 | (_x545 << 2))
#define _x586 (_x248 << 45)
#define _x587 (_x586 | (_x586 << 1))
#define _x588 (_x587 | (_x587 << 2))
#define _x589 (_x585 | _x588)
#define _x590 (_x584 | _x589)
#define _x591 (_x579 | _x590)
#define _x592 (_x206 | _x591)
    case 124: return _x592;
#define _x593 (x & 196608)
#define _x594 (_x593 << 16)
#define _x595 (_x594 | (_x594 << 2))
#define _x596 (x & 786432)
#define _x597 (_x596 << 18)
#define _x598 (_x597 | (_x597 << 2))
#define _x599 (_x595 | _x598)
#define _x600 (x & 3145728)
#define _x601 (_x600 << 20)
#define _x602 (_x601 | (_x601 << 2))
#define _x603 (x & 12582912)
#define _x604 (_x603 << 22)
#define _x605 (_x604 | (_x604 << 2))
#define _x606 (_x602 | _x605)
#define _x607 (_x599 | _x606)
#define _x608 (x & 50331648)
#define _x609 (_x608 << 24)
#define _x610 (_x609 | (_x609 << 2))
#define _x611 (x & 201326592)
#define _x612 (_x611 << 26)
#define _x613 (_x612 | (_x612 << 2))
#define _x614 (_x610 | _x613)
#define _x615 (x & 805306368)
#define _x616 (_x615 << 28)
#define _x617 (_x616 | (_x616 << 2))
#define _x618 (x & 3221225472)
#define _x619 (_x618 << 30)
#define _x620 (_x619 | (_x619 << 2))
#define _x621 (_x617 | _x620)
#define _x622 (_x614 | _x621)
#define _x623 (_x607 | _x622)
#define _x624 (_x222 | _x623)
    case 125: return _x624;
#define _x625 (x & 65536)
#define _x626 (_x625 << 16)
#define _x627 (_x626 | (_x626 << 1))
#define _x628 (x & 131072)
#define _x629 (_x628 << 17)
#define _x630 (_x629 | (_x629 << 1))
#define _x631 (_x627 | _x630)
#define _x632 (x & 262144)
#define _x633 (_x632 << 18)
#define _x634 (_x633 | (_x633 << 1))
#define _x635 (x & 524288)
#define _x636 (_x635 << 19)
#define _x637 (_x636 | (_x636 << 1))
#define _x638 (_x634 | _x637)
#define _x639 (_x631 | _x638)
#define _x640 (x & 1048576)
#define _x641 (_x640 << 20)
#define _x642 (_x641 | (_x641 << 1))
#define _x643 (x & 2097152)
#define _x644 (_x643 << 21)
#define _x645 (_x644 | (_x644 << 1))
#define _x646 (_x642 | _x645)
#define _x647 (x & 4194304)
#define _x648 (_x647 << 22)
#define _x649 (_x648 | (_x648 << 1))
#define _x650 (x & 8388608)
#define _x651 (_x650 << 23)
#define _x652 (_x651 | (_x651 << 1))
#define _x653 (_x649 | _x652)
#define _x654 (_x646 | _x653)
#define _x655 (_x639 | _x654)
#define _x656 (x & 16777216)
#define _x657 (_x656 << 24)
#define _x658 (_x657 | (_x657 << 1))
#define _x659 (x & 33554432)
#define _x660 (_x659 << 25)
#define _x661 (_x660 | (_x660 << 1))
#define _x662 (_x658 | _x661)
#define _x663 (x & 67108864)
#define _x664 (_x663 << 26)
#define _x665 (_x664 | (_x664 << 1))
#define _x666 (x & 134217728)
#define _x667 (_x666 << 27)
#define _x668 (_x667 | (_x667 << 1))
#define _x669 (_x665 | _x668)
#define _x670 (_x662 | _x669)
#define _x671 (x & 268435456)
#define _x672 (_x671 << 28)
#define _x673 (_x672 | (_x672 << 1))
#define _x674 (x & 536870912)
#define _x675 (_x674 << 29)
#define _x676 (_x675 | (_x675 << 1))
#define _x677 (_x673 | _x676)
#define _x678 (x & 1073741824)
#define _x679 (_x678 << 30)
#define _x680 (_x679 | (_x679 << 1))
#define _x681 (x & 2147483648)
#define _x682 (_x681 << 31)
#define _x683 (_x682 | (_x682 << 1))
#define _x684 (_x680 | _x683)
#define _x685 (_x677 | _x684)
#define _x686 (_x670 | _x685)
#define _x687 (_x655 | _x686)
#define _x688 (_x254 | _x687)
    case 126: return _x688;
    case 127: return x;
    default:
        UNREACHABLE();
        return 0;
    }
}


#if 0

def consecutive(S):
    for k in range(len(S)-1):
        if S[k] + 1 != S[k+1]:
            return False
    return True

def shift(x, k):
    if k == 0:
        return x
    if k < 0:
        return "(%s >> %d)" % (x,-k)
    return "(%s << %d)" % (x, k)

def hash(r, hashcons):
    if r in hashcons:
        return hashcons[r]
    id = "_x%d" % len(hashcons)
    print ("#define %s %s" % (id, r))
    hashcons[r] = id
    return id

def compile(S, offset, hashcons):
    if consecutive(S):
        k = S[0]
        l = len(S)
        if l == 64:
            return "x"
        mask = ((1 << l)-1) << k
        return hash(shift(hash("(x & %d)" % mask, hashcons), offset - k), hashcons)
    l2 = len(S) >> 1
    S1 = S[0:l2]
    S2 = S[l2:]
    if S1 == S2:
        r1 = compile(S1, offset, hashcons)        
        return hash("(%s | (%s << %d))" % (r1, r1, l2), hashcons)
    r1 = compile(S1, offset, hashcons)
    r2 = compile(S2, offset + l2, hashcons)
    return hash("(%s | %s)" % (r1, r2), hashcons)

def mems2index(mems, bound):
    k = 0
    i = 0
    for m in mems:
        if m:
            k |= (1 << i)
        i += 1
    k |= (1 << i)
    return k

def precompute(mems, bound, hashcons):
    K = 0
    j = 0
    coeff = {}
    deficit = {}
    for m in mems:
        if m:
            coeff[K] = (1 << j)
            deficit[K] = j - K
            K += 1
        j += 1
    indices = []
    for j in range(1 << len(mems)):
        k = 0
        for i in range(K):
            if 0 != (j & coeff[i]):
                k += (1 << i)
        indices += [k]
    idx = mems2index(mems, bound)
    instr = compile(indices, 0, hashcons)
    print("    case %d: return %s;" % (idx, instr))

def create_mems(mems, n):
    if n == 0:
        return ([], mems)
    prefix, m1 = create_mems(mems, n - 1)
    m2 = [m + [False] for m in m1]
    m3 = [m + [True] for m in m1]
    return prefix + m1, m2 + m3

def combinations(n, m, hashcons):
    prefix, S = create_mems([[]], 6)
    mems = prefix + S
    for mem in mems:
        precompute(mem, m, hashcons)

hashcons = {}
combinations(7, 7, hashcons)
        
#endif

