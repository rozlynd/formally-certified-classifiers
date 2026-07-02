
def export_vector(v: list)-> str:
    """
    Export a vector that would be given to a classifier, to a string format.

    Example :
    For the vector `[0.2, 1.3, 3.0, 5.1]`, the function must generate `V(0.2, 1.3, 3.0, 5.1)`
    """

    r = "V("

    ## construct the returned string element by element (with hex repr for floating numbers)
    for e in v:
        if isinstance(e, float):
            e_str = e.hex()
        else:
            e_str = str(e)
        r += e_str + ", "
    
    ## remove the last ", "
    if r[-2:] == ", ":
        r = r[:-2]
    
    r += ")"

    return r



