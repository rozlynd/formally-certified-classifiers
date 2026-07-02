
class ResultObj:

    __axps: list
    __cxps: list

    def __init__(self, _axps=None, _cxps=None):
        axps = _axps
        cxps = _cxps
    
    def __repr__(self):
        return "ResultObj(axps, cxps)"

    def get_axps(self):
        return self.__axps
    
    def get_cxps(self):
        return self.__cxps
    
    def set_axps(self, _axps):
        self.__axps = _axps
    
    def set_cxps(self, _cxps):
        self.__cxps = _cxps

