set pagination off
set confirm off
set breakpoint pending on
break nexa_fn_inspectValues
run
bt
info registers
continue
quit
