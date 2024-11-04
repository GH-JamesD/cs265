ANY_OFFSET = "any"

class HeapLoc():
    def __init__(self, idx, offset=0):
        self.idx = idx
        self.offset = offset
    
    def update_offset(self, offset):
        if self.offset == ANY_OFFSET:
            return 
        if offset == ANY_OFFSET:
            self.offset = ANY_OFFSET
            return
        self.offset += offset

    def meet(self, other):
        if self.idx != other.idx:
            raise ValueError("Cannot meet two different heap locations")
        if (self.offset == other.offset) and (self.offset != ANY_OFFSET):
            return HeapLoc(self.idx, self.offset)
        return HeapLoc(self.idx, ANY_OFFSET)
    
    def intersect(self, other):
        if self.idx != other.idx:
            raise ValueError("Cannot intersect two different heap locations")
        if self.offset == ANY_OFFSET:
            return other
        if other.offset == ANY_OFFSET:
            return self
        if self.offset == other.offset:
            return self
        return None

    def must_alias(self, other):
        if self.offset == ANY_OFFSET or other.offset == ANY_OFFSET:
            return False
        return self.idx == other.idx and self.offset == other.offset
    
    def may_alias(self, other):
        if self.idx == other.idx:
            return self.offset == ANY_OFFSET or other.offset == ANY_OFFSET or self.offset == other.offset
    
    def __repr__(self):
        return f"heap{self.idx}[{self.offset}]"

    def __str__(self):
        return repr(self)
    
    def __eq__(self, other):
        return self.idx == other.idx and self.offset == other.offset
    
class AliasLattice(dict):
    @classmethod
    def union(cls, *args):
        if any(arg.all_heap for arg in args):
            return AliasLattice("ALL_HEAP")
        ss = {}
        for arg in args:
            for idx, mem_loc in arg.items():
                if idx in ss:
                    ss[idx] = ss[idx].meet(mem_loc)
                else:
                    ss[idx] = mem_loc
        return AliasLattice(ss.values())
    
    # @classmethod
    # def intersect(cls, *args):
    #     if all(arg.all_heap for arg in args):
    #         return AliasLattice(ALL_HEAP)
    #     nontrivial_states = list(filter(lambda s: not s.all_heap, args))
    #     if not nontrivial_states:
    #         return AliasLattice({})
    #     ss = nontrivial_states[0]
    #     for arg in nontrivial_states[1:]:
    #         for idx, mem_loc in ss.items():
    #             if idx in arg: 
    #                 offset1 = mem_loc.offset
    #                 offset2 = arg[idx].offset
    #                 if offset2 == "any":
    #                     mem_loc.offset = "any"
    #                 elif offset1 == "any":
    #                     mem_loc.offset = offset2
    #                 elif offset1 != offset2:
    #                     del ss[idx]
    #             else:
    #                 del ss[idx]

    #     return AliasLattice(ss)


    def __init__(self, args=[]):
        if args == "ALL_HEAP":
            self.all_heap = True
            super().__init__()
        else:
            self.all_heap = False
            super().__init__({loc.idx: loc for loc in args})
    
    def may_alias(self, other):
        if self.all_heap or other.all_heap:
            return True
        for idx, mem_loc in self.items():
            if idx in other:
                if mem_loc.may_alias(other[idx]):
                    return True
        return False
    
    def must_alias(self, other):
        if self.all_heap or other.all_heap:
            return False
        for idx, mem_loc in self.items():
            if not ((idx in other) and mem_loc.must_alias(other[idx])):
                return False
        return True

    def __repr__(self):
        if self.all_heap:
            return "A(ALL_HEAP)"
        return "A(" + ','.join([repr(mem_loc) for mem_loc in self.values()]) + ")"

    def __str__(self):
        if self.all_heap:
            return repr(self)
        return ','.join([str(mem_loc) for mem_loc in self.values()]) + ")"
    
    def copy(self):
        if self.all_heap:
            return AliasLattice("ALL_HEAP")
        return AliasLattice(self.values())
    
    def __iter__(self):
        return iter(self.values())