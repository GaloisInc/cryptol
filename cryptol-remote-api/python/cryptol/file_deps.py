from typing import Dict, Any

def nestedFileDeps(getDeps : Any, name : str, isFile : bool) -> Any:
  done : Dict[str,Any]  = {}
  start = getDeps(name, isFile)
  todo  = start["imports"].copy()
  while len(todo) > 0:
    m = todo.pop()
    if m in done:
      continue
    deps = getDeps(m, False)
    todo.extend(deps["imports"])
  return (start, deps)

