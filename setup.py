"""
pyeb

Copyright (c) Nestor Catano

All rights reserved.

MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the ""Software""), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED *AS IS*, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
"""

from setuptools import setup, find_packages

setup(
        name='pyeb',
        version='1.0.62',
        author='Nestor Catano',
        author_email='nestor.catano@gmail.com',
        license='MIT License',
        packages=find_packages('src'),
        package_dir={'': 'src'},
        install_requires=[
            'z3-solver==4.13.0.0',
            'antlr4-tools',
            'antlr4-python3-runtime>=4.13.1'
            ],
        entry_points = {
             'console_scripts': [
                 'pyeb = pyeb.main:main',
                 ]
             },
        url='https://github.com/ncatanoc/pyeb',
        description='A refinement calculus implementation of Event-B in Python.',
        long_description=(open('README.md').read()),
        long_description_content_type="text/markdown",
        classifiers=[
            'Development Status :: 2 - Pre-Alpha',
            'Environment :: Console',
            'Intended Audience :: Developers',
            'License :: OSI Approved :: MIT License',
            'Operating System :: OS Independent',
            'Programming Language :: Python :: 3 :: Only',
            'Topic :: Software Development',
            ],
        )
