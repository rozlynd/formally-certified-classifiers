
def flatten_str_list(l: list[str])-> str:
    """
    Flatten a list of str `l` to get one string.\n
    Example :\n
        >>> flatten_str_list(["a", "b"])
        "ab"
    """
    res = ""
    for e in l:
        res += e + '\n'
    return res

def list_from_string(s: str)-> list:
    """
    Create a list from the a string representation of a list.\n   
    Keep the elements of the list as sting elements.\n
    Raise `AssertionError` if the first meaningful char of `s` is not `'['`, and if the last is not `']'`.\n
    Example :
    ```
    >>> list_from_string("[1, 2, string]")
    ["1", "2", "string"]
    ```
    """
    s = s.strip()
    assert s[0] == '['
    assert s[-1] == ']'
    s = s[1:-1]
    s = s.split(',')
    return [ e.strip() for e in s ]

def write_str_in_file(filename: str, text: str)-> None:
    """Write the string `text` in the file `filename`."""
    with open(filename, 'w') as f:
        f.write(text)






