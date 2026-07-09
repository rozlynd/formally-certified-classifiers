
def export_features(v: list, feature_names = None)-> str:
    """
    Export, to a string format, features from a vector by looking at the length of the vector.

    Example :
    For the vector `[0.2, 1.3, 0., 5.1]`, the function must generate `F(float, float, float, float)`
    Note that the only feature type supported by sklearn is `float`.

    To see how categorical features are represented, see :
    https://scikit-learn.org/stable/modules/preprocessing.html#encoding-categorical-features
    """

    feature_names = list(feature_names)
    are_features_nammed = feature_names != None or feature_names != []

    def get_feature_name(i):
        """Format the potential feature name.
        If name is defined, return name + " : ".
        Else, return "".
        """
        if are_features_nammed and feature_names[i] != "":
            return '"' + feature_names[i] + '" : '
        else: return ""

    r = "F(\n"
    prefix = "\t"
    suffix = ",\n"

    ## check that each element has type `float` (and construct the returned string)
    for i, e in enumerate(v):
        if i >= len(v)-1:
            suffix = "\n"
        e_str = prefix
        e_str += get_feature_name(i)
        if isinstance(e, float):
            e_str += "float"
        else:
            raise TypeError("Error in export_features : features must be of type float.")
        r += e_str + suffix
    
    r += ")"

    return r
