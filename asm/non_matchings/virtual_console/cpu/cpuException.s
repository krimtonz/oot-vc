glabel cpuException
/* 8000CFFC 000085BC  94 21 FF F0 */	stwu r1, -0x10(r1)
/* 8000D000 000085C0  7C 08 02 A6 */	mflr r0
/* 8000D004 000085C4  90 01 00 14 */	stw r0, 0x14(r1)
/* 8000D008 000085C8  93 E1 00 0C */	stw r31, 0xc(r1)
/* 8000D00C 000085CC  7C 9F 23 78 */	mr r31, r4
/* 8000D010 000085D0  93 C1 00 08 */	stw r30, 8(r1)
/* 8000D014 000085D4  7C 7E 1B 78 */	mr r30, r3
/* 8000D018 000085D8  80 03 0A AC */	lwz r0, 0xaac(r3)
/* 8000D01C 000085DC  54 00 07 7D */	rlwinm. r0, r0, 0, 0x1d, 0x1e
/* 8000D020 000085E0  41 82 00 0C */	beq lbl_8000D02C
/* 8000D024 000085E4  38 60 00 00 */	li r3, 0
/* 8000D028 000085E8  48 00 02 10 */	b lbl_8000D238
lbl_8000D02C:
/* 8000D02C 000085EC  2C 04 FF FF */	cmpwi r4, -1
/* 8000D030 000085F0  40 82 00 0C */	bne lbl_8000D03C
/* 8000D034 000085F4  38 60 00 00 */	li r3, 0
/* 8000D038 000085F8  48 00 02 00 */	b lbl_8000D238
lbl_8000D03C:
/* 8000D03C 000085FC  2C 04 00 10 */	cmpwi r4, 0x10
/* 8000D040 00008600  41 80 00 0C */	blt lbl_8000D04C
/* 8000D044 00008604  2C 04 00 16 */	cmpwi r4, 0x16
/* 8000D048 00008608  40 81 00 14 */	ble lbl_8000D05C
lbl_8000D04C:
/* 8000D04C 0000860C  2C 04 00 18 */	cmpwi r4, 0x18
/* 8000D050 00008610  41 80 00 14 */	blt lbl_8000D064
/* 8000D054 00008614  2C 04 00 1E */	cmpwi r4, 0x1e
/* 8000D058 00008618  41 81 00 0C */	bgt lbl_8000D064
lbl_8000D05C:
/* 8000D05C 0000861C  38 60 00 00 */	li r3, 0
/* 8000D060 00008620  48 00 01 D8 */	b lbl_8000D238
lbl_8000D064:
/* 8000D064 00008624  2C 04 00 0A */	cmpwi r4, 0xa
/* 8000D068 00008628  40 82 00 0C */	bne lbl_8000D074
/* 8000D06C 0000862C  38 60 00 00 */	li r3, 0
/* 8000D070 00008630  48 00 01 C8 */	b lbl_8000D238
lbl_8000D074:
/* 8000D074 00008634  2C 04 00 00 */	cmpwi r4, 0
/* 8000D078 00008638  40 82 00 90 */	bne lbl_8000D108
/* 8000D07C 0000863C  81 23 0A AC */	lwz r9, 0xaac(r3)
/* 8000D080 00008640  54 A4 44 2E */	rlwinm r4, r5, 8, 0x10, 0x17
/* 8000D084 00008644  81 03 0A B4 */	lwz r8, 0xab4(r3)
/* 8000D088 00008648  38 C0 00 00 */	li r6, 0
/* 8000D08C 0000864C  55 20 07 7D */	rlwinm. r0, r9, 0, 0x1d, 0x1e
/* 8000D090 00008650  80 E3 0A B0 */	lwz r7, 0xab0(r3)
/* 8000D094 00008654  7C 80 FE 70 */	srawi r0, r4, 0x1f
/* 8000D098 00008658  7D 04 23 78 */	or r4, r8, r4
/* 8000D09C 0000865C  90 83 0A B4 */	stw r4, 0xab4(r3)
/* 8000D0A0 00008660  7C E0 03 78 */	or r0, r7, r0
/* 8000D0A4 00008664  54 A7 06 3E */	clrlwi r7, r5, 0x18
/* 8000D0A8 00008668  90 03 0A B0 */	stw r0, 0xab0(r3)
/* 8000D0AC 0000866C  41 82 00 0C */	beq lbl_8000D0B8
/* 8000D0B0 00008670  38 00 00 00 */	li r0, 0
/* 8000D0B4 00008674  48 00 00 44 */	b lbl_8000D0F8
lbl_8000D0B8:
/* 8000D0B8 00008678  55 20 07 FF */	clrlwi. r0, r9, 0x1f
/* 8000D0BC 0000867C  40 82 00 0C */	bne lbl_8000D0C8
/* 8000D0C0 00008680  38 00 00 00 */	li r0, 0
/* 8000D0C4 00008684  48 00 00 34 */	b lbl_8000D0F8
lbl_8000D0C8:
/* 8000D0C8 00008688  3C A0 00 01 */	lis r5, 0x0000FF00@ha
/* 8000D0CC 0000868C  7C C4 46 70 */	srawi r4, r6, 8
/* 8000D0D0 00008690  38 A5 FF 00 */	addi r5, r5, 0x0000FF00@l
/* 8000D0D4 00008694  7C E0 FE 70 */	srawi r0, r7, 0x1f
/* 8000D0D8 00008698  7D 25 28 38 */	and r5, r9, r5
/* 8000D0DC 0000869C  54 A5 C0 3E */	rotlwi r5, r5, 0x18
/* 8000D0E0 000086A0  7C 80 00 38 */	and r0, r4, r0
/* 8000D0E4 000086A4  50 C5 C0 0E */	rlwimi r5, r6, 0x18, 0, 7
/* 8000D0E8 000086A8  7C A4 38 38 */	and r4, r5, r7
/* 8000D0EC 000086AC  7C 80 03 78 */	or r0, r4, r0
/* 8000D0F0 000086B0  30 80 FF FF */	addic r4, r0, -1
/* 8000D0F4 000086B4  7C 04 01 10 */	subfe r0, r4, r0
lbl_8000D0F8:
/* 8000D0F8 000086B8  2C 00 00 00 */	cmpwi r0, 0
/* 8000D0FC 000086BC  40 82 00 24 */	bne lbl_8000D120
/* 8000D100 000086C0  38 60 00 00 */	li r3, 0
/* 8000D104 000086C4  48 00 01 34 */	b lbl_8000D238
lbl_8000D108:
/* 8000D108 000086C8  80 83 00 20 */	lwz r4, 0x20(r3)
/* 8000D10C 000086CC  80 03 00 00 */	lwz r0, 0(r3)
/* 8000D110 000086D0  38 84 FF FC */	addi r4, r4, -4
/* 8000D114 000086D4  60 00 00 04 */	ori r0, r0, 4
/* 8000D118 000086D8  90 83 00 20 */	stw r4, 0x20(r3)
/* 8000D11C 000086DC  90 03 00 00 */	stw r0, 0(r3)
lbl_8000D120:
/* 8000D120 000086E0  80 83 00 00 */	lwz r4, 0(r3)
/* 8000D124 000086E4  54 80 06 F7 */	rlwinm. r0, r4, 0, 0x1b, 0x1b
/* 8000D128 000086E8  54 80 07 76 */	rlwinm r0, r4, 0, 0x1d, 0x1b
/* 8000D12C 000086EC  90 03 00 00 */	stw r0, 0(r3)
/* 8000D130 000086F0  40 82 00 18 */	bne lbl_8000D148
/* 8000D134 000086F4  7F C3 F3 78 */	mr r3, r30
/* 8000D138 000086F8  4B FF F9 E5 */	bl cpuHackHandler
/* 8000D13C 000086FC  80 1E 00 00 */	lwz r0, 0(r30)
/* 8000D140 00008700  60 00 00 10 */	ori r0, r0, 0x10
/* 8000D144 00008704  90 1E 00 00 */	stw r0, 0(r30)
lbl_8000D148:
/* 8000D148 00008708  80 7E 00 24 */	lwz r3, 0x24(r30)
/* 8000D14C 0000870C  3C 03 00 01 */	addis r0, r3, 1
/* 8000D150 00008710  28 00 FF FF */	cmplwi r0, 0xffff
/* 8000D154 00008714  41 82 00 34 */	beq lbl_8000D188
/* 8000D158 00008718  80 BE 00 20 */	lwz r5, 0x20(r30)
/* 8000D15C 0000871C  38 E0 FF FF */	li r7, -1
/* 8000D160 00008720  80 9E 0A B4 */	lwz r4, 0xab4(r30)
/* 8000D164 00008724  3C 00 80 00 */	lis r0, 0x8000
/* 8000D168 00008728  38 C5 FF FC */	addi r6, r5, -4
/* 8000D16C 0000872C  38 A0 00 00 */	li r5, 0
/* 8000D170 00008730  7C 80 03 78 */	or r0, r4, r0
/* 8000D174 00008734  90 FE 00 24 */	stw r7, 0x24(r30)
/* 8000D178 00008738  90 DE 0A BC */	stw r6, 0xabc(r30)
/* 8000D17C 0000873C  90 BE 0A B8 */	stw r5, 0xab8(r30)
/* 8000D180 00008740  90 1E 0A B4 */	stw r0, 0xab4(r30)
/* 8000D184 00008744  48 00 00 14 */	b lbl_8000D198
lbl_8000D188:
/* 8000D188 00008748  80 7E 00 20 */	lwz r3, 0x20(r30)
/* 8000D18C 0000874C  38 00 00 00 */	li r0, 0
/* 8000D190 00008750  90 1E 0A B8 */	stw r0, 0xab8(r30)
/* 8000D194 00008754  90 7E 0A BC */	stw r3, 0xabc(r30)
lbl_8000D198:
/* 8000D198 00008758  80 FE 00 00 */	lwz r7, 0(r30)
/* 8000D19C 0000875C  38 1F FF FF */	addi r0, r31, -1
/* 8000D1A0 00008760  80 DE 0A AC */	lwz r6, 0xaac(r30)
/* 8000D1A4 00008764  57 E3 10 3A */	slwi r3, r31, 2
/* 8000D1A8 00008768  54 EA 06 6E */	rlwinm r10, r7, 0, 0x19, 0x17
/* 8000D1AC 0000876C  80 BE 0A B0 */	lwz r5, 0xab0(r30)
/* 8000D1B0 00008770  60 C8 00 02 */	ori r8, r6, 2
/* 8000D1B4 00008774  38 80 FF FF */	li r4, -1
/* 8000D1B8 00008778  7C A5 20 38 */	and r5, r5, r4
/* 8000D1BC 0000877C  80 FE 0A B4 */	lwz r7, 0xab4(r30)
/* 8000D1C0 00008780  38 C0 FF 83 */	li r6, -125
/* 8000D1C4 00008784  7C 64 FE 70 */	srawi r4, r3, 0x1f
/* 8000D1C8 00008788  7C E6 30 38 */	and r6, r7, r6
/* 8000D1CC 0000878C  28 00 00 02 */	cmplwi r0, 2
/* 8000D1D0 00008790  7C C3 1B 78 */	or r3, r6, r3
/* 8000D1D4 00008794  7C A0 23 78 */	or r0, r5, r4
/* 8000D1D8 00008798  91 5E 00 00 */	stw r10, 0(r30)
/* 8000D1DC 0000879C  91 1E 0A AC */	stw r8, 0xaac(r30)
/* 8000D1E0 000087A0  90 7E 0A B4 */	stw r3, 0xab4(r30)
/* 8000D1E4 000087A4  90 1E 0A B0 */	stw r0, 0xab0(r30)
/* 8000D1E8 000087A8  41 81 00 10 */	bgt lbl_8000D1F8
/* 8000D1EC 000087AC  3C 00 80 00 */	lis r0, 0x8000
/* 8000D1F0 000087B0  90 1E 00 20 */	stw r0, 0x20(r30)
/* 8000D1F4 000087B4  48 00 00 10 */	b lbl_8000D204
lbl_8000D1F8:
/* 8000D1F8 000087B8  3C 60 80 00 */	lis r3, 0x80000180@ha
/* 8000D1FC 000087BC  38 03 01 80 */	addi r0, r3, 0x80000180@l
/* 8000D200 000087C0  90 1E 00 20 */	stw r0, 0x20(r30)
lbl_8000D204:
/* 8000D204 000087C4  80 1E 00 00 */	lwz r0, 0(r30)
/* 8000D208 000087C8  7F C4 F3 78 */	mr r4, r30
/* 8000D20C 000087CC  38 A0 FF FF */	li r5, -1
/* 8000D210 000087D0  60 00 00 24 */	ori r0, r0, 0x24
/* 8000D214 000087D4  90 1E 00 00 */	stw r0, 0(r30)
/* 8000D218 000087D8  80 6D 89 20 */	lwz r3, gSystem-_SDA_BASE_(r13)
/* 8000D21C 000087DC  80 63 00 58 */	lwz r3, 0x58(r3)
/* 8000D220 000087E0  48 05 03 F5 */	bl func_8005D614
/* 8000D224 000087E4  2C 03 00 00 */	cmpwi r3, 0
/* 8000D228 000087E8  40 82 00 0C */	bne lbl_8000D234
/* 8000D22C 000087EC  38 60 00 00 */	li r3, 0
/* 8000D230 000087F0  48 00 00 08 */	b lbl_8000D238
lbl_8000D234:
/* 8000D234 000087F4  38 60 00 01 */	li r3, 1
lbl_8000D238:
/* 8000D238 000087F8  80 01 00 14 */	lwz r0, 0x14(r1)
/* 8000D23C 000087FC  83 E1 00 0C */	lwz r31, 0xc(r1)
/* 8000D240 00008800  83 C1 00 08 */	lwz r30, 8(r1)
/* 8000D244 00008804  7C 08 03 A6 */	mtlr r0
/* 8000D248 00008808  38 21 00 10 */	addi r1, r1, 0x10
/* 8000D24C 0000880C  4E 80 00 20 */	blr 

