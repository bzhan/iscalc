from integral import expr


class Fixes:
    def __init__(self, fixes: dict = dict()):
        self.fixes = fixes

    def empty(self):
        return len(self.fixes.items()) == 0

    def export(self):
        res = []
        for a, b in self.fixes.items():
            if isinstance(b, expr.Type):
                res.append((a, str(b)))
            elif isinstance(b, dict):
                tmp = dict()
                tmp['params_name'] = b['params_name']
                tmp['func_type'] = str(b['func_type'])
                res.append(tmp)
        return res
