
def export_vector(v: list)-> str:
    """
    Export a vector that would be given to a classifier, to a string format.

    Example :
    For the vector `[0.2, 1.3, 3.0, 5.1]`, the function must generate `V(0.2, 1.3, 3.0, 5.1)`
    """

    r = "V(\n"

    prefix = "\t"
    suffix = ",\n"

    ## construct the returned string element by element (with hex repr for floating numbers)
    for i, e in enumerate(v):
        if i >= len(v)-1:
            suffix = "\n"
        
        e_str = prefix
        if isinstance(e, float):
            e_str += e.hex()
        else:
            e_str = str(e)
        r += e_str + suffix
    
    r += ")"

    return r



