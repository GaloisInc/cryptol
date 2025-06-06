import os
import sys
from cryptol.connection import connect
from junit_xml import TestSuite, TestCase

use_ansi_color = False

cry = connect(url="http://localhost:8080/", reset_server=True)

project_file = os.path.abspath(sys.argv[1]
                                if len(sys.argv) > 1
                                else "run-docstrings-data/project.toml")

project_dir = project_file
if not os.path.isdir(project_dir):
    project_dir = os.path.dirname(project_dir)

# Some colors to make things pretty
def ansi_color(a, y):
    if use_ansi_color:
        return "\033[" + a + "m" + y + "\033[0m"
    else:
        return y

def ok_color(x):
    return ansi_color("1;32",x)

def bad_color(x):
    return ansi_color("1;31",x)
    
def output_color(x):
    return ansi_color("36",x)

# Load the project, specifically modules containing untested docstrings
proj = cry.load_project(project_file, "untested").result()
cache_id = proj["cache_id"]

# See the current status of the files
known = {}
for obj in proj["test_results"]:
    if "file" in obj:
        known[obj["file"]] = obj["result"]


test_cases=[]

# Check if we need to test anything
for obj in proj["scan_status"]:
    if not "file" in obj:
        continue

    file = obj["file"]
    test_name = os.path.relpath(file, start=project_dir)
    test_case = TestCase(test_name, classname="Cryptol", file=file)

    # File does not contain errors
    if "scanned" in obj:
        s = obj["scanned"]

        # Do we need to run the tests?
        if not s["changed"] and file in known:
            
            result = known[file]
            if not result:
                test_case.status = "failure"
                test_case.add_failure_info("(cached)")
            else:
                test_case.stdout="(cached)"
            test_cases.append(test_case)
            continue

        output = []
        # Yes, we need to run the tests
        for m in s["parsed"]:
            mod = m["module"]
            cry.focus_module(mod)
            check = cry.check_docstrings(cache_id).result()
            cache_id = check["cache_id"]

            # Show results of testing each docstring
            for r in check["results"]:
                decl = r["name"]
                output.append(decl)

                # Each fance block in the docstrings
                for fence in r["fences"]:
                    
                    # Each command in the sequence
                    for cmd in fence:
                        cmd_result = cmd["result"]
                        ok = cmd_result["success"]
                        color = ok_color if ok else bad_color
                        output.append(color("  " + cmd["input"]))
                        for l in cmd["log"].splitlines():
                            output.append(output_color("    " + l))
                            
                        if not ok:
                            test_case.status = "failure"
                            test_case.add_failure_info(decl)
        test_case.stdout = "\n".join(output)

    # we faild to load the modules because they are invalid
    # (e.g., have parse errors)
    elif "invalid_module" in obj:
        test_case.status = "error"
        test_case.add_error_info(message=obj["invalid_module"]["error"])
    elif "invalid_dep" in obj:
        test_case.status = "error"
        test_case.add_error_info(message="Depends on a module with erorr")

    test_cases.append(test_case)

test_suite=TestSuite(os.path.dirname(os.path.relpath(project_file)), test_cases)
print(TestSuite.to_xml_string([test_suite]))
