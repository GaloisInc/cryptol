def nestedFileDeps(getDeps, name : str, isFile : bool) -> Any:
  done  = {}
  start = getDeps(name, isFile)
  todo  = start["imports"].copy()
  while len(todo) > 0:
    m = todo.pop()
    if m in done:
      continue
    deps = file_deps(m, False)
    todo.extend(deps["imports"])
  return (start, deps)

