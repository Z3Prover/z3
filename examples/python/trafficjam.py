from z3 import *

class Car():
    def __init__(self, is_vertical, base_pos, length, start, color):
        self.is_vertical = is_vertical          
        self.base = base_pos
        self.length = length
        self.start = start
        self.color = color

    def __eq__(self, other):
        return self.color == other.color

    def __ne__(self, other):
        return self.color != other.color

dimension = 6

red_car = Car(False, 2, 2, 3, "red")
cars = [
    Car(True, 0, 3, 0, 'yellow'),
    Car(False, 3, 3, 0, 'blue'),
    Car(False, 5, 2, 0, "brown"),
    Car(False, 0, 2, 1, "lgreen"),
    Car(True,  1, 2, 1, "light blue"),
    Car(True,  2, 2, 1, "pink"),
    Car(True,  2, 2, 4, "dark green"),
    red_car,
    Car(True,  3, 2, 3, "purple"),
    Car(False, 5, 2, 3, "light yellow"),
    Car(True,  4, 2, 0, "orange"),
    Car(False, 4, 2, 4, "black"),
    Car(True,  5, 3, 1, "light purple")
    ]

num_cars = len(cars)
B = BoolSort()
bv3 = BitVecSort(3)


state = Function('state', [ bv3 for c in cars] + [B])

def num(i):
    return BitVecVal(i,bv3)

def bound(i):
    return Const(cars[i].color, bv3)

fp = Fixedpoint()
fp.set("fp.engine","datalog")
fp.set("datalog.generate_explanations",True)
fp.declare_var([bound(i) for i in range(num_cars)])
fp.register_relation(state)

def mk_state(car, value):
    return state([ (num(value) if (cars[i] == car) else bound(i)) for i in range(num_cars)])

def mk_transition(row, col, i0, j, car0):
    body = [mk_state(car0, i0)]
    for index in range(num_cars):
        car = cars[index]
        if car0 != car:
            if car.is_vertical and car.base == col:
                for i in range(dimension):
                    if i <= row and row < i + car.length and i + car.length <= dimension:
                        body += [bound(index) != num(i)]
            if car.base == row and not car.is_vertical:
                for i in range(dimension):
                    if i <= col and col < i + car.length and i + car.length <= dimension:
                        body += [bound(index) != num(i)]

    s = "%s %d->%d" % (car0.color, i0, j)
    fp.rule(mk_state(car0, j), body, s)
    

def move_down(i, car):
    free_row = i + car.length
    if free_row < dimension:
        mk_transition(free_row, car.base, i, i + 1, car)
            

def move_up(i, car):
    free_row = i  - 1
    if 0 <= free_row and i + car.length <= dimension:
        mk_transition(free_row, car.base, i, i - 1, car)

def move_left(i, car):
    free_col = i - 1;
    if 0 <= free_col and i + car.length <= dimension:
        mk_transition(car.base, free_col, i, i - 1, car)


def move_right(i, car):
    free_col = car.length + i
    if free_col < dimension:
        mk_transition(car.base, free_col, i, i + 1, car)


# Initial state:
fp.fact(state([num(cars[i].start) for i in range(num_cars)]))

# Transitions:
for car in cars:
    for i in range(dimension):
        if car.is_vertical:
            move_down(i, car)
            move_up(i, car)
        else:
            move_left(i, car)
            move_right(i, car)
    

def get_instructions(ans):
    lastAnd = ans.arg(0).children()[-1]
    trace = lastAnd.children()[1]
    while trace.num_args() > 0:
        print(trace.decl())
        trace = trace.children()[-1]


goal = state([ (num(4) if cars[i] == red_car else bound(i)) for i in range(num_cars)])
fp.query(goal)
get_instructions(fp.get_answer())

del goal
del state
del fp

