# creates the model of a board game
# the board has WIDTH by HEIGHT squares
# start is on lowest row, middle square (or slightly left if even width
# from each square one can moveLeft: goes left with p=1/2 else forward with p=1/3 else right
#                          moveRight: goes right with p=1/2 else forward with p=1/3 else left
# if past the left or right side, you lose
# if past top side you win

import os


ASYMMETRIC = False
NONDETERMINISTIC = False

WIDTH = 3
HEIGHT = 1


def main():
    numsquares = WIDTH*HEIGHT
    squares = range(0, numsquares)
    lost = numsquares
    won = numsquares + 1
    start = WIDTH/2

    def left(square):
        if square % WIDTH == 0:
            return lost
        else:
            return square - 1

    def right(square):
        if (square + 1) % WIDTH == 0:
            return lost
        else:
            return square + 1

    def forward(square):
        if square / WIDTH == HEIGHT - 1:
            return won
        else:
            return square + WIDTH

    filename = 'board' + str(WIDTH) + 'x' + str(HEIGHT) + ('as' if ASYMMETRIC else '') + ('nd' if NONDETERMINISTIC else '') + '.txt'
    f = open(os.path.sep.join(['examples', 'boardgame', filename]), 'w')
    f.write('des(' + str(start) + ')\n')
    for square in squares:
        f.write('(' + str(square) + (', "move", ' if NONDETERMINISTIC else ', "moveLeft", ')
                + str(left(square)) + ' 1/2 ' + str(forward(square)) + ' 1/3 ' + str(right(square)) + ')\n')
        f.write('(' + str(square) + (', "move", ' if NONDETERMINISTIC else ', "moveRight", ')
                + str(right(square)) + (' 1/3 ' if ASYMMETRIC else ' 1/2 ') + str(forward(square)) + (' 1/2 ' if ASYMMETRIC else ' 1/3 ') + str(left(square)) + ')\n')

    f.write('(' + str(lost) + ', "lost", ' + str(lost) + ')\n')
    f.write('(' + str(won) + ', "won", ' + str(won) + ')\n')

    f.close()

main()
