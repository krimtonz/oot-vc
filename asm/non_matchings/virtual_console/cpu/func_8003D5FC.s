glabel cpuInvalidateCache
/* 8003D5FC 00038BBC  94 21 FF E0 */	stwu r1, -0x20(r1)
/* 8003D600 00038BC0  7C 08 02 A6 */	mflr r0
/* 8003D604 00038BC4  54 86 00 06 */	rlwinm r6, r4, 0, 0, 3
/* 8003D608 00038BC8  90 01 00 24 */	stw r0, 0x24(r1)
/* 8003D60C 00038BCC  3C 06 60 00 */	addis r0, r6, 0x6000
/* 8003D610 00038BD0  28 00 00 00 */	cmplwi r0, 0
/* 8003D614 00038BD4  93 E1 00 1C */	stw r31, 0x1c(r1)
/* 8003D618 00038BD8  7C BF 2B 78 */	mr r31, r5
/* 8003D61C 00038BDC  93 C1 00 18 */	stw r30, 0x18(r1)
/* 8003D620 00038BE0  7C 9E 23 78 */	mr r30, r4
/* 8003D624 00038BE4  93 A1 00 14 */	stw r29, 0x14(r1)
/* 8003D628 00038BE8  7C 7D 1B 78 */	mr r29, r3
/* 8003D62C 00038BEC  40 82 00 0C */	bne lbl_8003D638
/* 8003D630 00038BF0  38 60 00 01 */	li r3, 1
/* 8003D634 00038BF4  48 00 00 2C */	b lbl_8003D660
lbl_8003D638:
/* 8003D638 00038BF8  4B FC F6 E1 */	bl cpuFreeCachedAddress
/* 8003D63C 00038BFC  2C 03 00 00 */	cmpwi r3, 0
/* 8003D640 00038C00  40 82 00 0C */	bne lbl_8003D64C
/* 8003D644 00038C04  38 60 00 00 */	li r3, 0
/* 8003D648 00038C08  48 00 00 18 */	b lbl_8003D660
lbl_8003D64C:
/* 8003D64C 00038C0C  7F A3 EB 78 */	mr r3, r29
/* 8003D650 00038C10  7F C4 F3 78 */	mr r4, r30
/* 8003D654 00038C14  7F E5 FB 78 */	mr r5, r31
/* 8003D658 00038C18  48 00 0F AD */	bl func_8003E604
/* 8003D65C 00038C1C  38 60 00 01 */	li r3, 1
lbl_8003D660:
/* 8003D660 00038C20  80 01 00 24 */	lwz r0, 0x24(r1)
/* 8003D664 00038C24  83 E1 00 1C */	lwz r31, 0x1c(r1)
/* 8003D668 00038C28  83 C1 00 18 */	lwz r30, 0x18(r1)
/* 8003D66C 00038C2C  83 A1 00 14 */	lwz r29, 0x14(r1)
/* 8003D670 00038C30  7C 08 03 A6 */	mtlr r0
/* 8003D674 00038C34  38 21 00 20 */	addi r1, r1, 0x20
/* 8003D678 00038C38  4E 80 00 20 */	blr 
