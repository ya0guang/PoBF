import numpy as np
import argparse
import urllib.request
import yaml

url = 'https://gist.githubusercontent.com/yrevar/942d3a0ac09ec9e5eb3a/raw/238f720ff059c1f82f368259d1ca4ffa5dd8f9f5/imagenet1000_clsidx_to_labels.txt'


def main(args):
    # Prepare the label.
    if args.label_path is None:
        print("[+] Downloading the label...")
        output = urllib.request.urlopen(url).read().decode('utf-8')
        image_net_labels = yaml.load(output, Loader=yaml.FullLoader)
        print('[+] Labels downloaded.')

    n = args.number
    filepath = args.filepath
    output = args.output
    prediction = np.fromfile(filepath, dtype="float32")
    # Sort the array by the value and get the index of the maximum value.
    indices = np.argsort(prediction)[::-1][:n]

    # Get the labels.
    output_labels = [(image_net_labels[x], prediction[x]) for x in indices]
    print('[+] The prediction is\n\t{}'.format("\n\t".join([str(x)
          for x in output_labels])))

    # Store the output.
    print('[+] Storing the output to', output)
    with open(output, "w") as f:
        f.write(str(output_labels))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        prog='A simple interpreter for the prediction of ResNet, MobileNet')
    parser.add_argument(
        'filepath', help='The path of the output array of the TVM neural network')
    parser.add_argument(
        '-n', '--number', help='Show top n ImageNet labels', default=5, type=int)
    parser.add_argument('-l', '--label_path',
                        help='The path of the ImageNet label.', default=None)
    parser.add_argument(
        '-o', '--output', help="The path of the output file.", default='./output.txt')

    args = parser.parse_args()

    main(args)
