#!/usr/bin/env python3
# -*- coding: utf-8 -*-
from typing import Set, Optional, NamedTuple

from .ssa import SSAFunction, SSABasicBlock, BlockAttrib


class InternalFuncRecover:
    """ breaks the identification of internal function out into its own space and doesn't mess
        with Function and BasicBlock objects it examines
    """
    class InternalFunc(NamedTuple):
        start_block: SSABasicBlock
        return_block: SSABasicBlock
        blocks: Set[SSABasicBlock]

        def __repr__(self):
            return f"<InternalFunc {self.start_block.offset:x}/{self.return_block.offset:x}, {len(self.blocks)}>"
    # <class

    def __init__(self, dispatch_func: SSAFunction):
        self.dispatch_func = dispatch_func

    def split_off(self):
        """ splits all internal functions off the dispatch function and returns them
        """
        new_funcs = [self._split_off(f) for f in self._identify_internal_functions()]

        # add call instructions
        # - this can be done only now after all functions have their correct blocks, otherwise outer functions
        #   would collect calls to inner functions

        # TODO, add dispatch func
        for func in new_funcs:
            for caller_block in func:
                for callee_block in caller_block.out_edges:
                    if callee_block.has_attrib(BlockAttrib.FuncStart):
                        jump_instr = caller_block.insns[-1]
                        assert jump_instr.insn.name == 'JUMP'

                        # mark caller block
                        caller_block.add_attrib(BlockAttrib.Caller)

        return new_funcs

    def _split_off(self, internal_func: InternalFunc) -> SSAFunction:
        """ splits internal_func of the dispatch func and returns it as SSAFunction
            - block are moved
        """
        new_func = SSAFunction(internal_func.start_block.offset, f"_internal_{internal_func.start_block.offset:#x}")

        # TODO, create Function.move_blocks() and do it in one shot
        self.dispatch_func.remove_blocks(internal_func.blocks)
        for block in sorted(internal_func.blocks, key=lambda b: b.offset):
            new_func.add_block(block)
            block.function = new_func

        return new_func

    def _identify_internal_functions(self):
        def return_block_filter(bb):
            if bb.stack_delta < 0 and len(bb.insns) > 0:
                last_inst = bb.insns[-1]
                if last_inst.insn.name == 'JUMP':
                    return True
            return False
        # <def

        internal_funcs = []
        for ret_block in filter(return_block_filter, self.dispatch_func.blocks):
            if start_block := self.find_func_start(ret_block):

                # mark the start/end blocks
                start_block.add_attrib(BlockAttrib.FuncStart)
                ret_block.add_attrib(BlockAttrib.FuncEnd)

                # find all blocks and create InternalFunc
                func_blocks = self.find_func_blocks(start_block, ret_block)
                new_internal_func = self.InternalFunc(start_block, ret_block, func_blocks)
                internal_funcs.append(new_internal_func)

        # verify subset relations and remove blocks from outer func
        internal_funcs.sort(key=lambda f: len(f.blocks))
        for short_ix, short_func in enumerate(internal_funcs):
            for long_func in internal_funcs[short_ix + 1:]:
                if intersect := short_func.blocks.intersection(long_func.blocks):

                    if intersect == short_func.blocks:          # short is subset of long -> long calls short
                        print(f"{short_func} part of {long_func}")
                        long_func.blocks.difference_update(short_func.blocks)
                    else:                                       # overlap
                        # verify that intersection is a shared function (both include it)
                        assert any(intersect == f.blocks for f in internal_funcs[:short_ix])

        return internal_funcs

    @staticmethod
    def find_func_blocks(start_block: SSABasicBlock, return_block: SSABasicBlock) -> Set[SSABasicBlock]:
        """ discovers all paths between start/end_block and returns the blocks as a set
        """
        func_blocks = {start_block}     # we don't collect paths

        queue = [[start_block]]         # list of paths
        while queue:
            path = queue.pop(0)
    
            path_end = path[-1]
            if path_end == return_block:
                func_blocks.update(path)
    
            else:
                for suc_block in path_end.out_edges:
                    if suc_block not in path:
                        queue.append(path + [suc_block])

        return func_blocks

    @staticmethod
    def find_func_start(ret_block: SSABasicBlock) -> Optional[SSABasicBlock]:
        """ breadth first search for the start block
            - returns the start block or None
        """
        queue   = [ret_block]
        visited = {ret_block: ret_block.stack_delta}    # visited keep also the stack_delta sum

        while queue:
            bb = queue.pop(0)
            for pre in bb.in_edges - visited.keys():
                visited[pre] = stack_delta = visited[bb] + pre.stack_delta
                queue.append(pre)

                if stack_delta == 0:
                    return bb

        return None
