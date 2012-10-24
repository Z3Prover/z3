############################################
# Copyright (c) 2012 Microsoft Corporation
# 
# Author: Leonardo de Moura (leonardo)
############################################

class MKException(Exception):
    def __init__(self, value):
        self.value = value
    def __str__(self):
        return repr(self.value)

