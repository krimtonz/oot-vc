glabel func_800B8A84
/* 800B8A84 000B4044  94 21 FF E0 */	stwu r1, -0x20(r1)
/* 800B8A88 000B4048  7C 08 02 A6 */	mflr r0
/* 800B8A8C 000B404C  90 01 00 24 */	stw r0, 0x24(r1)
/* 800B8A90 000B4050  34 01 00 08 */	addic. r0, r1, 8
/* 800B8A94 000B4054  93 E1 00 1C */	stw r31, 0x1c(r1)
/* 800B8A98 000B4058  3B E0 00 00 */	li r31, 0
/* 800B8A9C 000B405C  93 C1 00 18 */	stw r30, 0x18(r1)
/* 800B8AA0 000B4060  7C BE 2B 78 */	mr r30, r5
/* 800B8AA4 000B4064  93 A1 00 14 */	stw r29, 0x14(r1)
/* 800B8AA8 000B4068  7C 9D 23 78 */	mr r29, r4
/* 800B8AAC 000B406C  93 81 00 10 */	stw r28, 0x10(r1)
/* 800B8AB0 000B4070  7C 7C 1B 78 */	mr r28, r3
/* 800B8AB4 000B4074  40 82 00 0C */	bne lbl_800B8AC0
/* 800B8AB8 000B4078  3B E0 FF FC */	li r31, -4
/* 800B8ABC 000B407C  48 00 00 4C */	b lbl_800B8B08
lbl_800B8AC0:
/* 800B8AC0 000B4080  80 6D 85 04 */	lwz r3, lbl_8025CBC4-_SDA_BASE_(r13)
/* 800B8AC4 000B4084  38 80 00 40 */	li r4, 0x40
/* 800B8AC8 000B4088  38 A0 00 20 */	li r5, 0x20
/* 800B8ACC 000B408C  48 00 10 79 */	bl func_800B9B44
/* 800B8AD0 000B4090  2C 03 00 00 */	cmpwi r3, 0
/* 800B8AD4 000B4094  90 61 00 08 */	stw r3, 8(r1)
/* 800B8AD8 000B4098  40 82 00 0C */	bne lbl_800B8AE4
/* 800B8ADC 000B409C  3B E0 FF EA */	li r31, -22
/* 800B8AE0 000B40A0  48 00 00 28 */	b lbl_800B8B08
lbl_800B8AE4:
/* 800B8AE4 000B40A4  93 A3 00 20 */	stw r29, 0x20(r3)
/* 800B8AE8 000B40A8  38 A0 00 00 */	li r5, 0
/* 800B8AEC 000B40AC  38 00 00 02 */	li r0, 2
/* 800B8AF0 000B40B0  80 81 00 08 */	lwz r4, 8(r1)
/* 800B8AF4 000B40B4  93 C4 00 24 */	stw r30, 0x24(r4)
/* 800B8AF8 000B40B8  80 81 00 08 */	lwz r4, 8(r1)
/* 800B8AFC 000B40BC  90 A4 00 28 */	stw r5, 0x28(r4)
/* 800B8B00 000B40C0  90 03 00 00 */	stw r0, 0(r3)
/* 800B8B04 000B40C4  93 83 00 08 */	stw r28, 8(r3)
lbl_800B8B08:
/* 800B8B08 000B40C8  2C 1F 00 00 */	cmpwi r31, 0
/* 800B8B0C 000B40CC  40 82 00 14 */	bne lbl_800B8B20
/* 800B8B10 000B40D0  80 61 00 08 */	lwz r3, 8(r1)
/* 800B8B14 000B40D4  7F A4 EB 78 */	mr r4, r29
/* 800B8B18 000B40D8  4B FF FA E9 */	bl func_800B8600
/* 800B8B1C 000B40DC  7C 7F 1B 78 */	mr r31, r3
lbl_800B8B20:
/* 800B8B20 000B40E0  7F E3 FB 78 */	mr r3, r31
/* 800B8B24 000B40E4  83 E1 00 1C */	lwz r31, 0x1c(r1)
/* 800B8B28 000B40E8  83 C1 00 18 */	lwz r30, 0x18(r1)
/* 800B8B2C 000B40EC  83 A1 00 14 */	lwz r29, 0x14(r1)
/* 800B8B30 000B40F0  83 81 00 10 */	lwz r28, 0x10(r1)
/* 800B8B34 000B40F4  80 01 00 24 */	lwz r0, 0x24(r1)
/* 800B8B38 000B40F8  7C 08 03 A6 */	mtlr r0
/* 800B8B3C 000B40FC  38 21 00 20 */	addi r1, r1, 0x20
/* 800B8B40 000B4100  4E 80 00 20 */	blr 
