import r2pipe
import os

r2 = r2pipe.open("/Users/RyanGoluch/Desktop/xinu_x86.elf")
r2.cmd("aaaa")

functions = []

with open("x86_functions.txt", "r") as f:
    x = f.readline()
    while x: 
        y = x.split(' ')
        y = y[len(y)-1]
        # print(y)
        functions.append(y)
        x = f.readline()
    f.close()

ext = "dot"

for z in functions: 
    #print(z)
    r2.cmd("s "+str(z))
    s = str(z).split('.')
    print(s)
    if len(s) == 1:
        temp = os.path.join("", s[0].replace("\n", "") + "." + ext)
    else:
        temp = os.path.join("", s[1].replace("\n", "") + "." + ext)
    r2.cmd("agfd > "+str(temp))


# print(len(functions))
