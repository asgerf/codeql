import argparse


def parse(args):
    parser = argparse.ArgumentParser()

    parser.add_argument("--csv")
    parser.add_argument("--xml")

    parser.add_argument("progname", help="file to run as main program")
    parser.add_argument(
        "arguments", nargs=argparse.REMAINDER, help="arguments to the program"
    )

    return parser.parse_args(args)
