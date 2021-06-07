#include "mips.h"
#include "tree.h"
#include "cpu.h"
#include "cache.h"
#include "system.h"

s32 cpuTreeTake(recomp_node_t**, u32*, size_t);
s32 treeInsertNode(recomp_node_t** root, s32 n64_start_addr, s32 n64_end_addr, recomp_node_t** new_node);
s32 treeAdjustRoot(cpu_class_t* cpu, s32 n64_start_addr, s32 n64_end_addr);
s32 treeBalance(recomp_tree_t* tree);
s32 treeSearchNode(recomp_node_t* node, s32 n64_addr, recomp_node_t** out_node);
s32 treePrintNode(cpu_class_t* cpu, recomp_node_t* node, s32 arg2, s32* start, s32* end);

#define NON_MATCHING
#ifdef NON_MATCHING
s32 treeCallerCheck(cpu_class_t *cpu, recomp_node_t *node, s32 arg2, s32 start_addr, s32 end_addr) {
    ext_call_t *ext_call;
    s32 i;
    u32 flg;
    
    if(node->ext_call_cnt == 0) {
        return 0;
    }

    if(node->ext_calls != NULL) {
        for(i = 0, ext_call = node->ext_calls; i < node->ext_call_cnt; ext_call++, i++) {
            u32 *code = ext_call->vc_addr;
            s32 addr = ext_call->n64_addr;
            if(addr >= start_addr && addr <= end_addr && code != NULL) {
                u32 *buf = code - (((arg2 == 0 ? 0 : 1) != 0) + 2);
                buf[0] = 0x3CA00000 | ((u32)addr >> 0x10);
                buf[1] = 0x60A50000 | ((u32)addr & 0xFFFF);
                
                *code = 0x48000001 | (((u32)cpu->execute_call - (u32)code) & 0x3FFFFFC);
                ext_call->vc_addr = NULL;
                DCStoreRange(buf, 0x10);
                ICInvalidateRange(buf, 0x10);
            }
        }
    }

    return 1;
}
#else
s32 treeCallerCheck(cpu_class_t *cpu, recomp_node_t *node, s32 arg2, s32 start_addr, s32 end_addr);
#pragma GLOBAL_ASM("asm/non_matchings/virtual_console/tree/treeCallerCheck.s")
#endif
#undef NON_MATCHING

s32 treeInit(cpu_class_t* cpu, u32 code_boundary) {
    recomp_tree_t* tree = cpu->recomp_tree;
    if (tree == NULL) {
        return 0;
    }
    tree->node_cnt = 0;
    tree->total_size = 0;
    tree->code_boundary = code_boundary;
    tree->n64_start = 0x00000000;
    tree->n64_end = 0x80000000;
    tree->code_root = NULL;
    tree->ovl_root = NULL;
    tree->unk_0x70 = 0;
    tree->unk_0x74 = 0;
    tree->root_to_clean = 0;
    tree->unk_0x7C = NULL;
    tree->unk_0x80 = 0;
    return 1;
}

s32 treeInitNode(recomp_node_t** out_node, recomp_node_t* parent, u32 n64_start_addr, u32 n64_end_addr) {
    recomp_node_t* new_node;
    u32 unk38;

    if (!cpuTreeTake(&new_node, &unk38, sizeof(recomp_node_t))) {
        return 0;
    }

    new_node->n64_start_addr = n64_start_addr;
    new_node->n64_end_addr = n64_end_addr;
    new_node->ext_calls = NULL;
    new_node->ext_call_cnt = 0;
    new_node->state = 0x21; // todo: create enum
    new_node->unk_0x00 = 0;
    new_node->recompiled_func = NULL;
    new_node->branch_cnt = 0;
    new_node->branches = NULL;
    new_node->checksum = 0;
    new_node->unk_0x28 = 1;
    new_node->size = 0;
    new_node->alloc_type = -1; // todo: create enum
    new_node->unk_0x34 = -1;
    new_node->unk_0x38 = unk38;
    new_node->parent = parent;
    new_node->left = NULL;
    new_node->right = NULL;
    *out_node = new_node;
    return 1;
}

inline s32 freeCPUBlk(recomp_node_t *node) {
    u32 *blk;
    u32 mask;
    u32 idx;

    if(node->unk_0x38 == -1) {
        return 0;
    }

    blk = gSystem->cpu->tree_blk_status;
    idx = (node->unk_0x38 >> 5) & 0x7FF;

    mask = ((1 << (node->unk_0x38 >> 0x10)) - 1) << (node->unk_0x38 & 0x1F);
    if((blk[idx] & mask) == mask) {
        blk[idx] &= ~mask;
        return 1;
    }

    return 0;
}

inline void printNode2(cpu_class_t *cpu, recomp_node_t *node) {
    recomp_tree_t *tree = cpu->recomp_tree;

    s32 start = node->n64_start_addr;
    s32 end = node->n64_end_addr;
    if(tree->code_root != NULL) {
        treePrintNode(cpu, tree->code_root, 0x10, &start, &end);
    }

    if(tree->ovl_root != NULL) {
        treePrintNode(cpu, tree->ovl_root, 0x10, &start, &end);
    }
}

#ifdef NON_MATCHING
inline s32 __treeKillInl(cpu_class_t *cpu, recomp_node_t *node) {
    if(node->recompiled_func != NULL) {
        printNode2(cpu, node);
    }

    cpu->recomp_tree->total_size -= node->size + 0x48;

}

s32 treeKill(cpu_class_t *cpu) {
    s32 tmp1 = 0;
    recomp_tree_t *tree = cpu->recomp_tree;

    if(tree->code_root != NULL) {
        tmp1 += treeKillNodes(cpu, tree->code_root);
        __treeKillInl(cpu, tree->code_root);
        if(tree->code_root->recompiled_func != NULL) {
            cpuHeapFree(cpu, tree->code_root);
        }

        if(!freeCPUBlk(tree->code_root)) {
            return 0;
        }
        tmp1++;
    }

    if(tree->ovl_root != NULL) {
        tmp1 += treeKillNodes(cpu, tree->ovl_root);
        __treeKillInl(cpu, tree->ovl_root);

        if(tree->ovl_root->recompiled_func != NULL) {
            cpuHeapFree(cpu, tree->ovl_root);
        }

        if(!freeCPUBlk(tree->ovl_root)) {
            return 0;
        }

        tmp1++;
    }

    tree->node_cnt -= tmp1;

    if(!xlHeapFree(&cpu->recomp_tree)) {
        return 0;
    }

    cpu->recomp_tree = NULL;
    return 1;
}
#else
#pragma GLOBAL_ASM("asm/non_matchings/virtual_console/tree/treeKill.s")
#endif

s32 treeKillNodes(cpu_class_t *cpu, recomp_node_t *node) {
    recomp_node_t *tmp2;
    recomp_node_t *tmp4;
    recomp_node_t *tmp1;
    s32 ret = 0;

    if(node == NULL) {
        return 0;
    }

    tmp1 = node;

    do {
        while(tmp1->left != NULL) {
            tmp1 = tmp1->left;
        }

        do {
            if(tmp1->right != NULL) {
                tmp1 = tmp1->right;
                break;
            }

            if(tmp1 == node) {
                return ret;
            }
            
            while(tmp2 = tmp1->parent, tmp1 != tmp2->left) {
                recomp_node_t *tmp4 = tmp1;
                tmp1 = tmp2;
                if(!func_80031D4C(cpu, tmp4, 2)) {
                    if(tmp4->recompiled_func != NULL) {
                        printNode2(cpu, tmp4);
                    }

                    cpu->recomp_tree->total_size -= tmp4->size + 0x48;

                    if(tmp4->recompiled_func != NULL) {
                        cpuHeapFree(cpu, tmp4);
                    }

                }

                if(!freeCPUBlk(tmp4)) {
                    return 0;
                }

                ret++;

                if(tmp2 == node) {
                    return ret;
                }

                tmp2 = tmp1->parent;
            }

            tmp4 = tmp1;
            tmp1 = tmp2;
            if(!func_80031D4C(cpu, tmp4, 2)) {
                if(tmp4->recompiled_func != NULL) {
                    printNode2(cpu, tmp4);
                }

                cpu->recomp_tree->total_size -= tmp4->size + 0x48;

                if(tmp4->recompiled_func != NULL) {
                    cpuHeapFree(cpu, tmp4);
                }

            }

            if(!freeCPUBlk(tmp4)) {
                return 0;
            }

            ret++;
        } while(tmp2 != NULL);
    } while(tmp1 != NULL);

    return ret;
}

s32 treeDeleteNode(cpu_class_t *cpu, recomp_node_t **arg1, recomp_node_t *node_to_delete) {
    recomp_tree_t *tree = cpu->recomp_tree;
    recomp_node_t *right;
    recomp_node_t *left;
    recomp_node_t *parent;

    if(node_to_delete == NULL) {
        return 0;
    }

    tree->node_cnt--;
    parent = node_to_delete->parent;
    left = node_to_delete->left;
    right = node_to_delete->right;

    if(parent != NULL) {
        if(left != NULL) {
            if(parent->left == node_to_delete) {
                parent->left = left;
            } else {
                parent->right = left;
            }

                
            left->parent = parent;
            
            if(right != NULL) {
                while(left->right != NULL) {
                    left = left->right;
                }

                left->right = right;
                right->parent = left;
            }
        } else if (right != NULL) {
            if(parent->left == node_to_delete) {
                parent->left = right;
            } else {
                parent->right = right;
            }

            right->parent = parent;
        } else {
            if(parent->left == node_to_delete) {
                parent->left = NULL;
            } else {
                parent->right = NULL;
            }
        }
    } else if (left != NULL) {
        *arg1 = left;
        if(tree->code_root == node_to_delete) {
            tree->code_root = left;
        } else {
            tree->ovl_root = left;
        }

        left->parent = NULL;
        if(right != NULL) {
            while(left->right != NULL) {
                left = left->right;
            }
            left->right = right;
            right->parent = left;
        }
    } else if (right != NULL) {
        *arg1 = right;
        if(tree->code_root == node_to_delete) {
            tree->code_root = right;
        } else {
            tree->ovl_root = right;
        }
        right->parent = NULL;
    } else {
        *arg1 = NULL;
        if(tree->code_root == node_to_delete) {
            tree->code_root = NULL;
        } else {
            tree->ovl_root = NULL;
        }
    }

    if(tree->n64_start == node_to_delete->n64_start_addr) {
        if(right != NULL) {
            while(right->left != NULL) {
                right = right->left;
            }
            tree->n64_start = right->n64_start_addr;
        } else if (parent != NULL) {
            tree->n64_start = parent->n64_start_addr;
        } else {
            tree->n64_start = tree->code_boundary;
        }
    }

    if(tree->n64_end == node_to_delete->n64_end_addr) {
        if(left != NULL) {
            while(left->right != NULL) {
                left = left->right;
            }
            tree->n64_end = left->n64_end_addr;
        } else if(parent != NULL) {
            tree->n64_end = parent->n64_end_addr;
        } else {
            tree->n64_end = tree->code_boundary;
        }
    }

    if(!func_80031D4C(cpu, node_to_delete, 2)) {
        if(node_to_delete->recompiled_func != NULL) {
            printNode2(cpu, node_to_delete);
        }

        cpu->recomp_tree->total_size -= node_to_delete->size + 0x48;

        if(node_to_delete->recompiled_func != NULL) {
            cpuHeapFree(cpu, node_to_delete);
        }
    }

    return !!freeCPUBlk(node_to_delete);
}

inline s32 inlfunc_8003F330(cpu_class_t *cpu, recomp_node_t *node) {
    recomp_node_t *tmp;
    if(!!cpuFreeCachedAddress(cpu, node->n64_start_addr, node->n64_end_addr) == 0) {
        return 0;
    }

    return !!treeDeleteNode(cpu, &tmp, node);
}

s32 func_8003F330(cpu_class_t *cpu, recomp_node_t *node) {
    recomp_node_t *tmp;
    if(!!cpuFreeCachedAddress(cpu, node->n64_start_addr, node->n64_end_addr) == 0) {
        return 0;
    }

    return !!treeDeleteNode(cpu, &tmp, node);
}

s32 treeInsert(cpu_class_t* cpu, s32 n64_start_addr, s32 n64_end_addr) {
    recomp_tree_t* tree = cpu->recomp_tree;
    recomp_node_t* new_node;
    s32 node_added;

    if (tree == NULL) {
        return 0;
    }

    if (n64_start_addr < tree->code_boundary && n64_end_addr > tree->code_boundary) {
        treeAdjustRoot(cpu, n64_start_addr, n64_end_addr);
    }

    tree->node_cnt++;
    tree->total_size += sizeof(recomp_node_t);

    if (n64_start_addr != 0x80000180) {
        if (n64_start_addr < tree->n64_start) {
            tree->n64_start = n64_start_addr;
        }

        if (n64_end_addr > tree->n64_end) {
            tree->n64_end = n64_end_addr;
        }
    }

    if (n64_start_addr < tree->code_boundary) {
        node_added = treeInsertNode(&tree->code_root, n64_start_addr, n64_end_addr, &new_node);
    } else if (n64_start_addr > tree->code_boundary) {
        node_added = treeInsertNode(&tree->ovl_root, n64_start_addr, n64_end_addr, &new_node);
    } else {
        return 0;
    }
    if (node_added) {
        return treeBalance(tree);
    } else {
        return 0;
    }
}

s32 treeInsertNode(recomp_node_t** root, s32 n64_start_addr, s32 n64_end_addr, recomp_node_t** new_node) {
    recomp_node_t* node;
    recomp_node_t **tmp1 = root;

    if (*tmp1 == NULL) {
        if (treeInitNode(tmp1, NULL, n64_start_addr, n64_end_addr)) {
            *new_node = *tmp1;
            return 1;
        } else {
            return 0;
        }
    }

    do {
        node = *tmp1;
        if (n64_start_addr < node->n64_start_addr) {
            tmp1 = &node->left;
        } else if (n64_start_addr > node->n64_start_addr) {
            tmp1 = &node->right;
        } else {
            return 0;
        }
    } while(*tmp1 != NULL);

    if (treeInitNode(tmp1, node, n64_start_addr, n64_end_addr)) {
        *new_node = *tmp1;
        return 1;
    }

    return 0;
}

inline recomp_node_t *getLeftTip(recomp_node_t *node) {
    while(node->left != NULL) {
        node = node->left;
    }

    return node;
}

inline recomp_node_t *getRightTip(recomp_node_t *node) {
    while(node->right != NULL) {
        node = node->right;
    }

    return node;
}

#ifdef NON_MATCHING
s32 treeBalance(recomp_tree_t* tree) {
    recomp_node_t *start;
    recomp_node_t* node;
    s32 depth;
    recomp_node_t *tmp2;
    recomp_node_t *tmp;
    s32 i;

    for (i = 0; i < 2; i++) {
        start = (i == 0) ? tree->code_root : tree->ovl_root;

        if (start == NULL) {
            continue;
        }

        for (depth = 0, node = start; node->right != NULL; node = node->right) {
            depth++;
        }

        if (depth >= 12) {
            tmp = start->right;
            node = start;
            for (depth = depth / 2; depth != 0; depth--) {
                node = node->right;
            }

            node->parent->right = NULL;
            start->right = node;
            node->parent = start;

            node = getLeftTip(node);
            node->left = tmp;
            tmp->parent = node;
        }

        for (depth = 0, node = start; node->left != NULL; node = node->left) {
            depth++;
        }

        if (depth >= 12) {
            tmp2 = start->left;
            node = start;
            for (depth = depth / 2; depth != 0; depth--) {
                node = node->left;
            }

            node->parent->left = NULL;
            start->left = node;
            node->parent = start;

            node= getRightTip(node);

            node->right = tmp2;
            tmp2->parent = node;
        }
    }
    return 1;
}
#else
#pragma GLOBAL_ASM("asm/non_matchings/virtual_console/tree/treeBalance.s")
#endif

s32 treeAdjustRoot(cpu_class_t* cpu, s32 start, s32 end) {
    s32 new_boundary = end + 2;
    s32 tmp2 = 0;
    s32 tmp4 = 0;
    recomp_node_t *tmp1;
    s32 tmp_node_cnt;
    s32 tmp_total_size;
    recomp_tree_t *tree;
    s32 tmp_boundary;
    s32 addr;
    recomp_node_t *tmp3;;

    tree = cpu->recomp_tree;
    tmp3 = tmp1 = NULL;
    tmp_node_cnt = tree->node_cnt;
    tmp_total_size = tree->total_size;
    tmp_boundary = tree->code_boundary;
    addr = tree->code_boundary + 2;

    do {
        tmp1 = NULL;
        treeSearchNode(tree->ovl_root, addr, &tmp1);
        if(tmp1 != NULL) {
            if(tmp2 == 0) {
                tmp2 = addr;
            }

            tree->code_boundary = new_boundary;
            if(!treeInsert(cpu, tmp1->n64_start_addr, tmp1->n64_end_addr)) {
                return 0;
            }

            if(!treeSearchNode(tree->code_root, addr, &tmp3)) {
                return 0;
            }

            tmp3->unk_0x28 = tmp1->unk_0x28;
            tmp3->size = tmp1->size;
            if(tmp1->recompiled_func != NULL) {
                tmp3->recompiled_func = tmp1->recompiled_func;
                tmp1->recompiled_func = NULL;
            }

            tmp3->branch_cnt = tmp1->branch_cnt;
            if(tmp1->branches != NULL) {
                tmp3->branches = tmp1->branches;
                tmp1->branches = NULL;
            }

            tmp3->checksum = tmp1->checksum;
            tmp3->state = tmp1->state;
            tmp3->ext_call_cnt = tmp1->ext_call_cnt;
            if(tmp1->ext_call_cnt != 0) {
                tmp3->ext_calls = tmp1->ext_calls;
                tmp1->ext_calls = NULL;
            }

            addr = tmp1->n64_end_addr;
            tree->code_boundary = tmp_boundary;
            tmp4 += treeKillRange(cpu, tree->ovl_root, tmp1->n64_start_addr, tmp1->n64_end_addr - 4);
        }

        addr += 4;
    } while(addr <= end);

    tree->code_boundary = new_boundary;
    tree->node_cnt = tmp_node_cnt;
    tree->total_size = tmp_total_size;
    return 1;
}

s32 treeSearchNode(recomp_node_t* node, s32 n64_addr, recomp_node_t** out_node) {
    if (node == NULL) {
        return 0;
    }

    do {
        if (n64_addr >= node->n64_start_addr && n64_addr < node->n64_end_addr) {
            *out_node = node;
            return 1;
        }

        if (n64_addr < node->n64_start_addr) {
            node = node->left;
        } else if (n64_addr > node->n64_start_addr) {
            node = node->right;
        } else {
            node = NULL;
        }
    } while (node != NULL);

    return 0;
}

s32 treeKillRange(cpu_class_t *cpu, recomp_node_t *node, s32 start, s32 end) {
    recomp_tree_t *tree = cpu->recomp_tree;
    recomp_node_t *tmp1 = NULL;
    s32 tmp3 = 0;
    s32 ret = 0;
    recomp_node_t *tmp2 = NULL;
    recomp_node_t *left;
    recomp_node_t *right;
    recomp_node_t *parent;
    s32 killed;

    if(start < tree->n64_start && end < tree->n64_start) {
        return 0;
    }

    if(start > tree->n64_end && end > tree->n64_end) {
        return 0;
    }

    do {
        treeSearchNode(node, start, &tmp1);
        if(tmp1 != NULL) {
            break;
        }

        start += 4;
    } while (start < end);  

    if(tmp1 != NULL) {
        parent = tmp1->parent;
        tmp1->parent = NULL;
        left = tmp1->left;
        tmp1->left = NULL;
        right = tmp1->right;
        while(right != NULL) {
            if(right->n64_start_addr < end) {
                if(right->n64_end_addr == tree->n64_end) {
                    tmp3 = 1;
                }
                right = right->right;
            } else {
                if(right != NULL) {
                    right->parent->right = NULL;
                }
                break;
            }
            
        }

        if(parent != NULL) {
            if(left != NULL) {
                if(parent->left == tmp1) {
                    parent->left = left;
                } else {
                    parent->right = left;
                }

                left->parent = parent;

                if(right != NULL) {
                    while(left->right != NULL) {
                        left = left->right;
                    }

                    left->right = right;
                    right->parent = left;
                }
            } else if(right != NULL) {
                if(parent->left == tmp1) {
                    parent->left = right;
                } else {
                    parent->right = right;
                }

                right->parent = parent;
            } else {
                if(parent->left == tmp1) {
                    parent->left = NULL;
                } else {
                    parent->right = NULL;
                }
            }
        } else if(left != NULL) {
            node = left;
            if(tree->code_root == tmp1) {
                tree->code_root = left;
            } else {
                tree->ovl_root = left;
            }

            left->parent = NULL;
            if(right != NULL) {
                while(left->right != NULL) {
                    left = left->right;
                }

                left->right = right;
                right->parent = left;
            }
        } else if(right != NULL) {
            node = right;
            if(tree->code_root == tmp1) {
                tree->code_root = right;
            } else {
                tree->ovl_root = right;
            }

            right->parent = NULL;
        } else {
            node = NULL;

            if(tree->code_root == tmp1) {
                tree->code_root = NULL;
            } else {
                tree->ovl_root = NULL;
            }
        }

        if(tree->n64_start == tmp1->n64_start_addr) {
            if(right != NULL) {
                while(right->left != NULL) {
                    right = right->left;
                }

                tree->n64_start = right->n64_start_addr;
            } else if (parent != NULL) {
                tree->n64_start = parent->n64_start_addr;
            } else {
                tree->n64_start = tree->code_boundary;
            }
        }

        if(tmp3) {
            if(left != NULL) {
                while(left->right != NULL) {
                    left = left->right;
                }

                tree->n64_end = left->n64_end_addr;
            } else if(parent != NULL) {
                tree->n64_end = parent->n64_end_addr;
            } else {
                tree->n64_end = tree->code_boundary;
            }
        }

        ret = treeKillNodes(cpu, tmp1);
        if(!func_80031D4C(cpu, tmp1, 2)) {
            recomp_node_t *tmp4 = tmp1;
            if(tmp4->recompiled_func != NULL) {
                printNode2(cpu, tmp4);
            }

            cpu->recomp_tree->total_size -= tmp4->size + 0x48;

            if(tmp1->recompiled_func != NULL) {
                cpuHeapFree(cpu, tmp1);
            }
        }

        if(!freeCPUBlk(tmp1)) {
            return 0;
        }

        ret++;
    }

    do {
        treeSearchNode(node, end, &tmp2);
        if(tmp2 != NULL) {
            break;
        }
        end -= 4;
    } while(start < end);

    if(tmp2 != NULL) {
        parent = tmp2->parent;
        tmp2->parent = NULL;
        left = tmp2->left;
        right = tmp2->right;
        tmp2->right = NULL;
        while(left != NULL) {
            if(left->n64_start_addr > start) {
                    left = left->left;
            } else {
                if(left != NULL) {
                    left->parent->left = NULL;
                }
                break;
            }
        }

        if(parent != NULL) {
            if(right != NULL) {
                if(parent->left == tmp2) {
                    parent->left = right;
                } else {
                    parent->right = right;
                }
                right->parent = parent;
                if(left != NULL) {
                    while(right->left != NULL) {
                        right = right->left;
                    }

                    right->left = left;
                    left->parent = right;
                }
            } else if(left != NULL) {
                if(parent->left == tmp2) {
                    parent->left = left;
                } else {
                    parent->right = left;
                }
                left->parent = parent;
            } else {
                if(parent->left == tmp2) {
                    parent->left = NULL;
                } else {
                    parent->right = NULL;
                }
            }
        } else if(right != NULL) {
            if(tree->code_root == tmp2) {
                tree->code_root = right;
            } else {
                tree->ovl_root = right;
            }

            right->parent = NULL;
            if(left != NULL) {
                while(right->left != NULL) {
                    right = right->left;
                }

                right->left = left;
                left->parent = right;
            }
        } else if(left != NULL) {
            if(tree->code_root == tmp2) {
                tree->code_root = left;
            } else {
                tree->ovl_root = left;
            }

            left->parent = NULL;
        } else {
            if(tree->code_root == tmp2) {
                tree->code_root = NULL;
            } else {
                tree->ovl_root = NULL;
            }
        }

        if(tree->n64_end == tmp2->n64_end_addr) {
            if(left != NULL) {
                while(left->right != NULL) {
                    left = left->right;
                }

                tree->n64_end = left->n64_end_addr;
            } else if(parent != NULL) {
                tree->n64_end = parent->n64_end_addr;
            } else {
                tree->n64_end = tree->code_boundary;
            }
        }

        ret += treeKillNodes(cpu, tmp2);
        if(!func_80031D4C(cpu, tmp2, 2)) {
            recomp_node_t *tmp4 = tmp2;
            if(tmp4->recompiled_func != NULL) {
                printNode2(cpu, tmp4);
            }

            cpu->recomp_tree->total_size -= tmp4->size + 0x48;

            if(tmp2->recompiled_func != NULL) {
                cpuHeapFree(cpu, tmp2);
            }
        }

        if(!freeCPUBlk(tmp2)) {
            return 0;
        }

        ret++;
    }

    return ret;
}

s32 treeTimerCheck(cpu_class_t* cpu) {
    s32 start;
    s32 end;
    recomp_tree_t* tree;

    if (cpu->call_cnt > 0x7FFFF000) {
        tree = cpu->recomp_tree;
        if (tree->unk_0x70 != 0) {
            return 0;
        }

        end = 0x7FFFF000;
        start = 0;
        if (tree->code_root != NULL) {
            treePrintNode(cpu, tree->code_root, 0x100, &start, &end);
        }

        if (tree->ovl_root != NULL) {
            treePrintNode(cpu, tree->ovl_root, 0x100, &start, &end);
        }

        start = end - 3;
        if (tree->code_root != NULL) {
            treePrintNode(cpu, tree->code_root, 0x1000, &start, &end);
        }

        if (tree->ovl_root != NULL) {
            treePrintNode(cpu, tree->ovl_root, 0x1000, &start, &end);
        }

        cpu->call_cnt -= start;
        return 1;
    }

    return 0;
}

s32 func_80040258(cpu_class_t *cpu) {
    s32 tmp = cpu->call_cnt - 200;
    recomp_tree_t *tree = cpu->recomp_tree;
    recomp_node_t *node = cpu->running_node;
    
    tree->unk_0x70 = 0;
    tree->unk_0x7C = NULL;
    tree->unk_0x80 = 0;

    if(node != NULL && node->unk_0x28 > 0) {
        node->unk_0x28 = cpu->call_cnt;
    }

    if(tree->root_to_clean == 0) {
        if(tree->code_root != NULL) {
            treeForceCleanNodes(cpu, tree->code_root, tmp);
        }
    } else {
        if(tree->ovl_root != NULL) {
            treeForceCleanNodes(cpu, tree->ovl_root, tmp);
        }
    }

    tree->root_to_clean ^= 1;
    node = cpu->running_node;
    tree = cpu->recomp_tree;
    tree->unk_0x70 = 0;
    tree->unk_0x7C = NULL;
    tree->unk_0x80 = 0;

    if(node != NULL && node->unk_0x28 > 0) {
        node->unk_0x28 = cpu->call_cnt;
    }

    if(tree->root_to_clean == 0) {
        if(tree->code_root != NULL) {
            treeForceCleanNodes(cpu, tree->code_root, tmp);
        }
    } else {
        if(tree->ovl_root != NULL) {
            treeForceCleanNodes(cpu, tree->ovl_root, tmp);
        }
    }

    tree->root_to_clean ^= 1;

    return 1;

}

inline s32 cleanBothRoots(cpu_class_t *cpu, recomp_tree_t *tree) {
    s32 tmp2 = 0;
    s32 tmp1 = 0;

    if(tree->root_to_clean == 0) {
        tmp2 = treeCleanNodes(cpu, tree->code_root);
    }

    if(tree->root_to_clean != 0 || tmp2 != 0) {
        if(treeCleanNodes(cpu, tree->ovl_root)) {
            tmp1 = 1;
        }
    }

    return tmp1;
}

#define NNULLORZERO(p,m) ((p) != NULL ? (p)->m : 0)

s32 treeCleanup(cpu_class_t *cpu, recomp_tree_t *tree) {
    
    if(!cleanBothRoots(cpu, tree)) {
        return 0;
    }

    if(NNULLORZERO(cpu->recomp_tree, total_size) > 0x400000) {
        tree->unk_0x70 = cpu->call_cnt - 10;
    } else if(NNULLORZERO(cpu->recomp_tree, total_size) > 0x319750) {
        tree->unk_0x70 += 95;
        if(tree->unk_0x70 > cpu->call_cnt - 10) {
            tree->unk_0x70 = cpu->call_cnt - 10;
        }
    } else {
        tree->unk_0x70 = 0;
        tree->unk_0x7C = NULL;
        tree->unk_0x80 = 0;
    }

    return 1;
}

s32 treeCleanNodes(cpu_class_t *cpu, recomp_node_t *arg1) {
    recomp_node_t *tmp2 = arg1;
    recomp_node_t *tmp1 = NULL;
    recomp_tree_t *tree = cpu->recomp_tree;
    recomp_node_t *tmp3;
    s32 treeUnk70 = tree->unk_0x70;

    if(arg1 == NULL) {
        tree->root_to_clean ^= 1;
        return 1;
    }

    if(tree->unk_0x7C == NULL) {
        tree->unk_0x7C = arg1;
    }

    while(tree->unk_0x7C != NULL) {
        if(cpu->unk_0x3C == cpu->unk_0x40 && tree->unk_0x74 < 12) {
            if(tree->unk_0x80 == 0) {
                while(tree->unk_0x7C->left != NULL) {
                    tree->unk_0x7C = tree->unk_0x7C->left;
                }
                tree->unk_0x80 = 1;
            }

            while(tree->unk_0x7C != NULL) {
                if(cpu->unk_0x3C == cpu->unk_0x40 && tree->unk_0x74 < 12) {
                    if(tmp1 != NULL) {
                        if(!cpuFreeCachedAddress(cpu, tmp1->n64_start_addr, tmp1->n64_end_addr)) {
                            return 0;
                        }

                        if(!treeDeleteNode(cpu, &tmp2, tmp1)) {
                            return 0;
                        }

                        tmp1 = NULL;

                        tree->unk_0x74++;
                    }

                    if(tree->unk_0x7C->unk_0x28 > 0 && tree->unk_0x7C->unk_0x28 <= treeUnk70) {
                        tmp1 = tree->unk_0x7C;
                    }

                    if(tree->unk_0x7C->right != NULL) {
                        tree->unk_0x7C = tree->unk_0x7C->right;
                        tree->unk_0x80 = 0;
                        break;
                    }

                    if(tree->unk_0x7C == tmp2) {
                        if(tmp1 != NULL) {
                            if(!cpuFreeCachedAddress(cpu, tmp1->n64_start_addr, tmp1->n64_end_addr)) {
                                return 0;
                            }

                            if(!treeDeleteNode(cpu, &tmp2, tmp1)) {
                                return 0;
                            }
                        }

                        tree->root_to_clean ^= 1;
                        tree->unk_0x7C = NULL;
                        tree->unk_0x80 = 0;

                        return 1;
                    }

                    while(tree->unk_0x7C != tree->unk_0x7C->parent->left) {
                        tree->unk_0x7C = tree->unk_0x7C->parent;
                        if(tree->unk_0x7C == tmp2) {
                            if(tmp1 != NULL) {
                                if(!cpuFreeCachedAddress(cpu, tmp1->n64_start_addr, tmp1->n64_end_addr)) {
                                    return 0;
                                }

                                if(!treeDeleteNode(cpu, &tmp2, tmp1)) {
                                    return 0;
                                }

                            }

                            tree->root_to_clean ^= 1;
                            tree->unk_0x7C = NULL;
                            tree->unk_0x80 = 0;

                            return 1;
                        }
                    }

                    tree->unk_0x7C = tree->unk_0x7C->parent;
                    tree->unk_0x80 = 1;
                } else {
                    break;
                }
            }
        } else {
            break;   
        }
    }

    if(tmp1 != NULL) {
        if(!cpuFreeCachedAddress(cpu, tmp1->n64_start_addr, tmp1->n64_end_addr)) {
            return 0;
        }

        treeDeleteNode(cpu, &tmp2, tmp1);

        return 0;
    }

    return 0;
}

s32 treeForceCleanNodes(cpu_class_t *cpu, recomp_node_t *node, s32 arg2) {
    recomp_node_t *cur_node;
    recomp_node_t *tmp = NULL;
    recomp_node_t *tmp2 = node;

    if(node == NULL) {
        return 0;
    }
    cur_node = node;
    do {
        while(cur_node->left != NULL) {
            cur_node = cur_node->left;
        }

        do {
            if(tmp != NULL) {
                if(!cpuFreeCachedAddress(cpu, tmp->n64_start_addr, tmp->n64_end_addr)) {
                    return 0;
                }

                if(!treeDeleteNode(cpu, &tmp2, tmp)) {
                    return 0;
                }

                tmp = NULL;
            }

            if(cur_node->unk_0x28 > 0 && cur_node->unk_0x28 <=  arg2) {
                tmp = cur_node;
            }

            if(cur_node->right != NULL) {
                cur_node = cur_node->right;
                break;
            }

            if(cur_node == tmp2) {
                if(tmp != NULL) {
                    if(!cpuFreeCachedAddress(cpu, tmp->n64_start_addr, tmp->n64_end_addr)) {
                        return 0;
                    }

                    if(!treeDeleteNode(cpu, &tmp2, tmp)) {
                        return 0;
                    }
                }
                return 1;
            }

            while(cur_node != cur_node->parent->left) {
                cur_node = cur_node->parent;
                if(cur_node == tmp2) {
                    if(tmp != NULL) {
                        if(!cpuFreeCachedAddress(cpu, tmp->n64_start_addr, tmp->n64_end_addr)) {
                            return 0;
                        }

                        if(!treeDeleteNode(cpu, &tmp2, tmp)) {
                            return 0;
                        }
                    }

                    return 1;                
                }
            }
            cur_node = cur_node->parent;
        } while(cur_node != NULL);
    } while(cur_node != NULL);

    return 0;
}

s32 treePrintNode(cpu_class_t* cpu, recomp_node_t* node, s32 type, s32* val1, s32* val2) {
    u32 ra_has_ppc_reg;
    u32 flg0;
    u32 flg1;
    u32 flg2;
    u32 flg3;
    recomp_node_t *cur_node;
    s32 node_cnt = 0;

    if(node == NULL) {
        return 0;
    }

    cur_node = node;
    flg0 = type & 1;
    flg1 = type & 0x10;
    flg2 = type & 0x100;
    flg3 = type & 0x1000;
    ra_has_ppc_reg = (reg_map[MREG_RA] >> 8) & 1;

    do {
        while(cur_node->left != NULL) {
            cur_node = cur_node->left;
            node_cnt++;
            if(flg0 && node_cnt > *val1) {
                (*val1)++;
            }
        }

        do {
            if(flg1 != 0) {
                treeCallerCheck(cpu, cur_node, ra_has_ppc_reg, *val1, *val2);
            } else if(flg2) {
                if(cur_node->unk_0x28 > 0) {
                    if(cur_node->unk_0x28 > *val1) {
                        *val1 = cur_node->unk_0x28;
                    }

                    if(cur_node->unk_0x28 < *val2) {
                        *val2 = cur_node->unk_0x28;
                    }
                }
            } else if(flg3) {
                if(cur_node->unk_0x28 > 0) {
                    cur_node->unk_0x28 -= *val1;
                }
            }

            if(cur_node->right != NULL) {
                cur_node = cur_node->right;
                node_cnt++;
                if(flg0 && node_cnt > *val2) {
                    (*val2)++;
                }
                break;
            }

            if(cur_node == node) {
                return 1;
            }
            
            while(cur_node != cur_node->parent->left) {
                cur_node = cur_node->parent;
                node_cnt--;
                if(cur_node == node) {
                    return 1;
                }
            }
            cur_node = cur_node->parent;
        } while(cur_node != NULL);
    } while(cur_node != NULL);

    return 0;
}
