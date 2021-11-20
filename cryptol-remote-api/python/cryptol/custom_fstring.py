"""An interface for defining custom f-string wrappers"""

from typing import Any, Callable, Dict, List
import builtins
import ast
import sys

def customf(body : str, onAST : Callable[[ast.FormattedValue], List[ast.expr]],
            frames : int = 0, globals : Dict[str, Any] = {},
                              locals : Dict[str, Any] = {},
            filename : str = "<custom f-string>") -> str:
    """This function parses the given string as if it were an f-string,
    applies the given function to the AST of each of the formatting fields in
    the string, then evaluates the result to get the resulting string.
    
    By default, the global and local variables used in the call to ``eval``
    are the value of ``sys.__getframe(1+frames).f_globals`` and the value of
    ``sys.__getframe(1+frames).f_locals``, respectively. This is meant to
    ensure that the all the variables which were in scope when the custom
    f-string is formed are also in scope when it is evaluated. Thus, the value
    of ``frames`` should be incremented for each wrapper function defined
    around this function (e.g. see the definition of ``func_customf``).
    
    To add additional global or local variable values (which are combined with,
    but take precedence over, the values mentioned in the previous paragraph)
    use the ``globals`` and ``locals`` keyword arguments.
    """
    # Get the global/local variable context of the previous frame so the local
    #  names 'body', 'onAST', etc. aren't shadowed our the call to ``eval``
    previous_frame = sys._getframe(1 + frames)
    all_globals = {**previous_frame.f_globals, **globals}
    all_locals = {**previous_frame.f_locals, **locals}
    # The below line should be where any f-string syntax errors are raised
    tree = ast.parse('f' + str(repr(body)), filename=filename, mode='eval')
    if not isinstance(tree, ast.Expression) or not isinstance(tree.body, ast.JoinedStr):
       raise ValueError(f'Invalid custom f-string: {str(repr(body))}')
    joined_values : List[ast.expr] = []
    for node in tree.body.values:
        if isinstance(node, ast.FormattedValue):
            joined_values += onAST(node)
        else:
            joined_values += [node]
    tree.body.values = joined_values
    try:
        return str(eval(compile(tree, filename=filename, mode='eval'), all_globals, all_locals))
    except SyntaxError as e:
        # I can't think of a case where we would raise an error here, but if
        # we do it's worth telling the user that the column numbers are all
        # messed up
        msg = '\nNB: Column numbers refer to positions in the original string'
        raise type(e)(str(e) + msg).with_traceback(sys.exc_info()[2])

def func_customf(body : str, func : Callable,
                 frames : int = 0, globals : Dict[str, Any] = {},
                                   locals : Dict[str, Any] = {},
                 filename : str = "<custom f-string>",
                 func_id : str = "_func_customf__func_id") -> str:
    """Like ``customf``, but can be provided a function to apply to the values
    of each of the formatting fields before they are formatted as strings,
    instead of a function applied to their ASTs.
    """
    def onAST(node : ast.FormattedValue) -> List[ast.expr]:
        kwargs = {'lineno': node.lineno, 'col_offset': node.col_offset}
        func = ast.Name(id=func_id, ctx=ast.Load(), **kwargs)
        node.value = ast.Call(func=func, args=[node.value], keywords=[], **kwargs)
        return [node]
    return customf(body, onAST, frames=1+frames,
                                globals={**globals, func_id:func},
                                locals=locals,
                                filename=filename)
