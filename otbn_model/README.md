Run `python build.py` to build. It should generate a `build.ninja` file and invoke `ninja` on it.
Tested with `ninja` version `1.10.1`. Older version seems to silently fail, when `dyndep` is actually not supported.
