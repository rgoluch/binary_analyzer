import r2pipe
import os

functions = []

with open("shell_obj_files.txt", "r") as f:
    x = f.readline()
    while x: 
        y = x.split('\n')
        y = y[0]
        # y = x
        # print(y)
        functions.append(y)
        x = f.readline()
    f.close()

print(len(functions))
ext = "dot"

for z in functions: 
    t = z
    # z = "shell.o"
    # t = "object_files/"+t
    t = str(t)
    r2 = r2pipe.open(t)
    r2.cmd("aaaa")
    z = z.split('.')[0]
    #print(z)
    r2.cmd("s "+str("sym."+z))
    s = str(z).split('.')
    print(s)
    if len(s) == 1:
        temp = os.path.join("", s[0].replace("\n", "") + "." + ext)
    else:
        temp = os.path.join("", s[1].replace("\n", "") + "." + ext)
    r2.cmd("agfd > "+temp)



