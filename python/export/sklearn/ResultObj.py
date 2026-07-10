from utils import string_of_list


class ResultObj:

    __axps: list
    __cxps: list

    def __init__(self, _axps=None, _cxps=None):
        self.__axps = _axps
        self.__cxps = _cxps
    
    def __repr__(self):
        prefix = '\t'
        return (
            "ResultObj(\n" +
            f"{prefix}axps : {string_of_list(self.__axps, prefix)},\n" +
            f"{prefix}cxps : {string_of_list(self.__cxps, prefix)}" +
            "\n)"
        )

    def get_axps(self):
        return self.__axps
    
    def get_cxps(self):
        return self.__cxps
    
    def set_axps(self, _axps):
        self.__axps = _axps
    
    def set_cxps(self, _cxps):
        self.__cxps = _cxps

