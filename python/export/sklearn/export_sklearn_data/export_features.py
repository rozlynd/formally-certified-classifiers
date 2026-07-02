
def export_features(v: list)-> str:
    """
    Export, to a string format, features from a vector by looking at the length of the vector.

    Example :
    For the vector `[0.2, 1.3, 0., 5.1]`, the function must generate `F(float, float, float, float)`
    Note that the only feature type supported by sklearn is `float`.

    To see how categorical features are represented, see :
    https://scikit-learn.org/stable/modules/preprocessing.html#encoding-categorical-features
    """

    r = "F("

    ## check that each element has type `float` (and construct the returned string)
    for e in v:
        if isinstance(e, float):
            e_str = "float"
        else:
            raise TypeError("Error in export_features : features must be of type float.")
        r += e_str + ", "
    
    ## remove the last ", "
    if r[-2:] == ", ":
        r = r[:-2]
    
    r += ")"

    return r
