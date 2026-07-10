
def export_vector(v: list, prefix: str = '')-> str:
    """
    Export a vector that would be given to a classifier, to a string format.

    Example :
    For the vector `[0.2, 1.3, 3.0, 5.1]`, the function must generate `V(0.2, 1.3, 3.0, 5.1)`
    """

    r = prefix + "V(\n"

    inter_prefix = prefix + "\t"
    suffix = ",\n"

    ## construct the returned string element by element (with hex repr for floating numbers)
    for i, e in enumerate(v):
        if i >= len(v)-1:
            suffix = "\n"
        
        e_str = inter_prefix
        if isinstance(e, float):
            e_str += e.hex()
        else:
            e_str = str(e)
        r += e_str + suffix
    
    r += prefix + ")"

    return r

def export_vectors(vs: list[list])-> str:
    """
    Export a list of vectors that would be given to a classifier, to a string format.
    """

    r = "Vs(\n"

    prefix = "\t"
    suffix = ",\n"

    ## construct the returned string element by element (with hex repr for floating numbers)
    for i, v in enumerate(vs):
        if i >= len(vs)-1:
            suffix = "\n"
        
        r += export_vector(v, prefix) + suffix
    
    r += ")"

    return r


