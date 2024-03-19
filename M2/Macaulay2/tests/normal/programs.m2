fn = temporaryFileName()
fn << ///printf "Hello %s!" "$1"/// << close
name = baseFilename fn
dir = replace(name | "$", "", fn)
programPaths#name = dir

fileMode(0o644, fn)
program = findProgram(name, name, RaiseError => false)
assert(program === null)

fileMode(0o755, fn)
program = findProgram(name, name)
assert(program#"name" == name)
assert(program#"path" == dir)
assert(program#"prefix" == (".*", ""))
assert(net program == name)

pr = runProgram(program, "world", KeepFiles => true)
assert(pr#"command" == fn | " world")
assert(pr#"output" == "Hello world!")
assert(toString pr == "Hello world!")
assert(pr#"error" == "")
assert(pr#"return value" == 0)
assert(status pr == 0)
assert(get pr#"output file" == "Hello world!")
assert(get pr#"error file" == "")
assert(net pr == "0")

copyFile(fn, dir | "/foo-bar")
prefix = ("bar", "foo-")
program = findProgram(name, {name, "bar"}, Prefix => {prefix})
assert(program#"prefix" == prefix)

fn << "touch baz" << close
program = findProgram(name, name)
runProgram(program, name, RunDirectory => dir | "/foo/bar")
assert(fileExists(dir | "/foo/bar/baz"))

program = findProgram("foo", name, AdditionalPaths => {dir})
assert(program#"path" == dir)

-- test findProgram(String)
fn << "if [ $1 != \"--version\" ]; then exit 1; fi" << endl << close
program = findProgram name

-- test Program << Thing
fn << "read REPLY; echo $REPLY" << endl << close
assert Equation(toString(program << "foo"), "foo\n")

-- test runProgram(String, String)
assert Equation(toString runProgram("echo", "foo"), "foo\n")

fn << "echo 1.0" << endl << close
program = findProgram(name, name, MinimumVersion => ("0.9", name))
assert(program#"version" == "1.0")
program = findProgram(name, name, MinimumVersion => ("1.1", name),
    RaiseError => false)
assert(program === null)

-- https://github.com/Macaulay2/M2/issues/1503
newdir = dir | "foo (bar) baz"
makeDirectory newdir
copyFile(fn, newdir | "/" | name)
programPaths#name = newdir
findProgram(name, name)
programPaths#name = dir | ///foo\ \(bar\)\ baz///
findProgram(name, name)
