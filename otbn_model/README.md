Run `python3 build.py setup` to setup. It will check for some packages, which might need to be installed manually. Other than those, the script should install local versions of `dafny`, `vale` and `z3`.

Run `python3 build.py build` to generate the ninja file. 

Run `ninja -v -j4` to build. If everything works, there should be a file named `gen/run_modexp.elf` as the output.

Tested with `ninja` version `1.10.1`. Older version might silently fail, when `dyndep` is actually not supported.
