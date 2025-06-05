from cryptol.connection import connect
import os
import sys

cry = connect(url="http://localhost:8080/", reset_server=True)

project_file = os.path.abspath(sys.argv[1]
                                if len(sys.argv) > 1
                                else "run-docstrings-data/project.toml")
print("Using " + project_file)

# Some colors to make things pretty
def ok(x):
    return "\033[1;32m" + x + "\033[0m"
def bad(x):
    return "\033[1;31m" + x + "\033[0m"
def output(x):
    return "\033[36m" + x + "\033[0m"


# Load the project, specifically modules containing untested docstrings
proj = cry.load_project(project_file, "untested").result()
cache_id = proj["cache_id"]

# See the current status of the files
known = {}
for obj in proj["test_results"]:
    if "file" in obj:
        known[obj["file"]] = obj["result"]

# Check if we need to test anything
for obj in proj["scan_status"]:
    if not "file" in obj:
        continue

    file = obj["file"]
    print(file)

    # File does not contain errors
    if "scanned" in obj:
        s = obj["scanned"]

        # Do we need to run the tests?
        if not s["changed"] and file in known:
            result = known[file]
            print(2 * ' ' + "Unchanged:", ok("OK") if result else bad("FAIL"))
            continue

        # Yes, we need to run the tests
        for m in s["parsed"]:
          mod = m["module"]
          print(2*' ' + "module", mod)
          cry.focus_module(mod)
          check = cry.check_docstrings(cache_id).result()
          cache_id = check["cache_id"]

          # Show results of testing each docstring
          for r in check["results"]:
            print(4*' ' + "Docstring on", r["name"])

            # Each fance block in the docstrings
            for fence in r["fences"]:

                # Each command in the sequence
                for cmd in fence:
                    cmd_result = cmd["result"]
                    
                    # Show command
                    print(6 * ' ', (ok if cmd_result["success"] else bad)(cmd["input"]), sep="")

                    # Show output
                    for l in cmd["log"].splitlines():
                        print(8 * ' ',output(l), sep="")
                    
                    # Show result
                    val = cmd_result["value"]
                    if not val is None:
                        print(6 * ' ', val, sep="")
                    ty = cmd_result["type"]
                    if not ty is None:
                        print(6 * ' ', ty, sep="")

    # we faild to load the modules because they are invalid
    # (e.g., have parse errors)
    elif "invalid_module" in obj:
        print("  Error:", obj["invalid_module"]["error"])
    elif "invalid_dep" in obj:
        print("  Depends on a module with an error")

