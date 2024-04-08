#!/usr/bin/env python
# -*- coding: utf-8 -*-
# IsotopeDistributionCalculator.pyw

# Copyright (c) 2015-204, Nicolas Elie
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright
#   notice, this list of conditions and the following disclaimer.
# * Redistributions in binary form must reproduce the above copyright
#   notice, this list of conditions and the following disclaimer in the
#   documentation and/or other materials provided with the distribution.
# * Neither the name of the copyright holders nor the names of any
#   contributors may be used to endorse or promote products derived
#   from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS 'AS IS'
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED.  IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

import sys
import os
import yaml

from PySide6.QtCore import (QAbstractTableModel, QMimeData, Signal, Qt)
from PySide6.QtGui import (QIcon, QPixmap, QColor,  QAction)
from PySide6.QtWidgets import (QMainWindow, QComboBox, QApplication, QPushButton, QRadioButton,
                               QMessageBox, QWidget, QTableView, QButtonGroup, QCheckBox,
                               QColorDialog, QCompleter, QDoubleSpinBox, QHBoxLayout, QLabel,
                               QMenu, QSizePolicy, QSpinBox, QSplitter,
                               QVBoxLayout)

import matplotlib
from matplotlib.backends.backend_qtagg import (FigureCanvasQTAgg as FigureCanvas,
                                               NavigationToolbar2QT as NavigationToolbar)
from matplotlib.figure import Figure
from matplotlib.ticker import MultipleLocator
from dataclasses import astuple

import numpy as np
import re
import traceback
from decimal import Decimal, getcontext

try:
    from xml.etree import cElementTree as ElementTree
except:
    HAS_ELEMENTTREE = False
else:
    HAS_ELEMENTTREE = True
    
from molmass import Formula

MAX_FORMULAE = 10
DEFAULT_MZ_DIGITS = 4
DEFAULT_ABUNDANCE_DIGITS = 2
DEFAULT_MINIMUM_ABUNDANCE = 0.1 #%
DEFAULT_RESOLUTION = 20000
MINIMUM_RESOLUTION = 100
MAXIMUM_RESOLUTION = 1000000
DEFAULT_FWHM = 0.05
MINIMUM_FWHM = 0.001
MAXIMUM_FWHM = 5.0
DEFAULT_FORMULA = ''
SUBSCRIPT_NUMBER_RE = re.compile(r'([0-9]{1,})')
SUPERSCRIPT_CHARGE_RE = re.compile(r'([0-9]*[+\-]{1})')
X_AXIS_LABEL = 'm/z'
X_AXIS_LABEL_STYLE = 'italic'
Y_AXIS_LABEL = 'Normalized Abundance (%)'
Y_AXIS_LABEL_STYLE = ''
DEFAULT_CENTROID_COLOR = 'r'
DEFAULT_CENTROID_STYLE = '-'
DEFAULT_GAUSSIAN_COLOR = 'g'
DEFAULT_GAUSSIAN_STYLE = '-'
DEFAULT_GAUSSIAN_MARKER = ''
DEFAULT_PASTED_COLOR = 'b'
DEFAULT_PASTED_STYLE = '-'
DEFAULT_PASTED_MARKER = ''

####
# Borrowed from matplotlib.mlab
def normpdf(*args):
    """ Return the normal pdf evaluated at *x*; args provides *x*, *mu*, *sigma* """
    x, mu, sigma = args
    return 1./(np.sqrt(2*np.pi)*sigma)*np.exp(-0.5 * (1./sigma*(x - mu))**2)

def resource_path(relative_path):
    """ Get absolute path to resource, works for dev and for PyInstaller """
    if getattr(sys, 'frozen', False): # frozen
        base_path = sys._MEIPASS
    else: # unfrozen
        base_path = os.path.dirname(os.path.abspath(__file__))

    return os.path.join(base_path, relative_path)
    
APP_NAME = 'Isotope Distribution Calculator'

APP_ICON = resource_path('Atom.ico')
DRAW_ICON = resource_path('Bina-pencil-green.png')
ANNOTATE_THRESHOLD = 2.0
MASSHUNTER_MIMETYPE = 'application/x-qt-windows-mime;value="MH_QUAL_SPECTRA_XML"'
X_AXIS_LABEL_STYLE = X_AXIS_LABEL_STYLE if X_AXIS_LABEL_STYLE != '' else 'normal'
Y_AXIS_LABEL_STYLE = Y_AXIS_LABEL_STYLE if Y_AXIS_LABEL_STYLE != '' else 'normal'
if getattr(sys, 'frozen', False): # frozen
    CONFIG_FILE = os.path.splitext(os.path.realpath(sys.executable))[0] + '.yaml'
else: # unfrozen
    CONFIG_FILE = os.path.splitext(os.path.realpath(__file__))[0] + '.yaml'
getcontext().prec = 2 #precision on ppm error calculation

class AppForm(QMainWindow):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle(APP_NAME)
        self.setWindowIcon(QIcon(APP_ICON))
        
        self.load_config()
        
        self.create_menu()
        self.create_main_frame()

        self._data = None
        self._pasted_data = None
        self._formula = None
        self._last_invalid_formula = ''
        self._spectrum = None

    def load_config(self):
        self.options = {}
        if os.path.exists(CONFIG_FILE):
            with open(CONFIG_FILE, 'r') as f:
                self.options = yaml.safe_load(f)
            if self.options is None:
                self.options = {}
        
        if self.options.get('history', None) is None:
            self.options['history'] = [DEFAULT_FORMULA,]
        if self.options.get('show_grid', None) is None:
            self.options['show_grid'] = False
        if self.options.get('show_annotations', None) is None:
            self.options['show_annotations'] = True
        if self.options.get('show_centroid', None) is None:
            self.options['show_centroid'] = True
        if self.options.get('show_gaussian', None) is None:
            self.options['show_gaussian'] = False
        if self.options.get('gaussian_use_constant_fwhm', None) is None:
            self.options['gaussian_use_constant_fwhm'] = True
        if self.options.get('gaussian_constant_fwhm', None) is None:
            self.options['gaussian_constant_fwhm'] = DEFAULT_FWHM
        if self.options.get('gaussian_use_constant_resolution', None) is None:
            self.options['gaussian_use_constant_resolution'] = False
        if self.options.get('gaussian_constant_resolution', None) is None:
            self.options['gaussian_constant_resolution'] = DEFAULT_RESOLUTION
        if self.options.get('minimum_abundance', None) is None:
            self.options['minimum_abundance'] = DEFAULT_MINIMUM_ABUNDANCE
        if self.options.get('mz_digits', None) is None:
            self.options['mz_digits'] = DEFAULT_MZ_DIGITS
        if self.options.get('abundance_digits', None) is None:
            self.options['abundance_digits'] = DEFAULT_ABUNDANCE_DIGITS
        if self.options.get('centroid_color', None) is None:
            self.options['centroid_color'] = DEFAULT_CENTROID_COLOR
        if self.options.get('gaussian_color', None) is None:
            self.options['gaussian_color'] = DEFAULT_GAUSSIAN_COLOR
        if self.options.get('pasted_color', None) is None:
            self.options['pasted_color'] = DEFAULT_PASTED_COLOR
        if self.options.get('centroid_linestyle', None) is None:
            self.options['centroid_linestyle'] = DEFAULT_CENTROID_STYLE
        if self.options.get('gaussian_linestyle', None) is None:
            self.options['gaussian_linestyle'] = DEFAULT_GAUSSIAN_STYLE
        if self.options.get('pasted_linestyle', None) is None:
            self.options['pasted_linestyle'] = DEFAULT_PASTED_STYLE
        if self.options.get('gaussian_marker', None) is None:
            self.options['gaussian_marker'] = DEFAULT_GAUSSIAN_MARKER
        if self.options.get('pasted_marker', None) is None:
            self.options['pasted_marker'] = DEFAULT_PASTED_MARKER
            
    def closeEvent(self, event):
        self.options['history'] = []
        for i in range(0, self.formula_cbox.count()):
            self.options['history'].append(str(self.formula_cbox.itemText(i)))
        self.options['show_grid'] = self.grid_cb.isChecked()
        self.options['show_annotations'] = self.annotate_cb.isChecked()
        self.options['show_centroid'] = self.centroid_cb.isChecked()
        self.options['show_gaussian'] = self.gaussian_cb.isChecked()
        self.options['gaussian_use_constant_fwhm'] = self.fwhm_rb.isChecked()
        self.options['gaussian_constant_fwhm'] = self.fwhm_spinbox.value()
        self.options['gaussian_use_constant_resolution'] = self.resolution_rb.isChecked()
        self.options['gaussian_constant_resolution'] = self.resolution_spinbox.value()
        self.options['minimum_abundance'] = self.minabund_spinbox.value()
        self.options['mz_digits'] = self.mz_digits_spinbox.value()
        self.options['abundance_digits'] = self.abund_digits_spinbox.value()
        self.options['centroid_color'] = self.centroid_color_bt.color()
        self.options['gaussian_color'] = self.gaussian_color_bt.color()
        self.options['pasted_color'] = self.pasted_color_bt.color()
        self.options['centroid_linestyle'] = self.centroid_color_bt.lineStyle()
        self.options['gaussian_linestyle'] = self.gaussian_color_bt.lineStyle()
        self.options['pasted_linestyle'] = self.pasted_color_bt.lineStyle()
        self.options['gaussian_marker'] = self.gaussian_color_bt.lineMarker()
        self.options['pasted_marker'] = self.pasted_color_bt.lineMarker()
            
        with open(CONFIG_FILE, 'w') as f:
            yaml.dump(self.options, f)
        
        super().closeEvent(event)
        
    def save_plot(self):
        self.canvas.toolbar.save_figure()
    
    def copy_spectrum(self):
        if self._data is not None:
            clipboard = QApplication.clipboard() #Get clipboard
            mime = QMimeData() #Get mime data object
            clipboard.clear() #Clear clipboard
            
            pixmap = QPixmap.grabWidget(self.canvas) #Grab spectrum image
            mime.setImageData(pixmap) #Copy image to clipboard
            
            text = ''
            for x,y in self._data:
                text += '%f\t%f\n' % (x,y) #Get spectrum data as text
            mime.setText(text) #Copy text to clipboard
            clipboard.setMimeData(mime) #Special copy, set image and text to clipboard
            
    def paste_spectrum(self):
        def warn():
            QMessageBox.warning(self, 'Warning', 'Data in the clipboard was not recognized as a spectrum.')
            
        def warn_too_many_points():
            QMessageBox.warning(self, 'Warning', 'Too many data points, it would take too long time to plot.')
        
        clipboard = QApplication.clipboard()
        mime = clipboard.mimeData()
        if mime.hasFormat(MASSHUNTER_MIMETYPE): #MassHunter
            if HAS_ELEMENTTREE:
                xmldata = mime.data(MASSHUNTER_MIMETYPE)
                start = xmldata.indexOf('<?xml version="1.0" encoding="utf-8"?><MH_QUAL_SPECTRA_XML>')
                end = xmldata.indexOf('</MH_QUAL_SPECTRA_XML>')
                if start != 0 and end != 0:
                    xmldata = xmldata[start:end+22]
                    tree = ElementTree.fromstring(xmldata)
                    details = tree.find('details')
                    if details is not None:
                        ifxdata = details.find('IFxData')
                        if ifxdata is not None:
                            try:
                                data = np.array([[float(elem.attrib['x']), float(elem.attrib['y'])] for elem in ifxdata.findall('d')])
                                if data.shape[0] > 10000:
                                    warn_too_many_points()
                                    return
                                data[:,1] = data[:,1]/data[:,1].max()*100.0 #normalize
                                self._pasted_data = data
                            except:
                                type, value, last_traceback = sys.exc_info()
                                lines = traceback.format_exception(type, value, last_traceback)
                                QMessageBox.warning(self, 'Warning', 'Data was recognized as coming from MassHunter but the following error occured during processing: %s' % ''.join(lines))
                                return
                            else:
                                self.on_draw()
        elif mime.hasText(): #XCalibur/MassLynx/FleXanalysis
            text = mime.text()
            if text.startsWith('SPECTRUM - MS'): #XCalibur
                text = text.split('Intensity')[1]
            
            try:
                if '\t' in text:
                    data = np.fromstring(str(text), sep='\t')
                elif ' ' in text:
                    data = np.fromstring(str(text), sep=' ')
                else:
                    warn()
                    return
                data = data.reshape(data.shape[0]/2, 2)
                if data.shape[0] > 10000:
                    warn_too_many_points()
                    return
                max = data[:,1].max()
                max = max if max != 0 else 1
                data[:,1] = data[:,1]/max*100.0 #normalize
                self._pasted_data = data
            except:
                type, value, last_traceback = sys.exc_info()
                lines = traceback.format_exception(type, value, last_traceback)
                QMessageBox.warning(self, 'Warning', 'Data was recognized as coming from XCalibur, MassLynx or Flexanalysis but the following error occured during processing: %s' % ''.join(lines))
                return
            else:
                self.on_draw()
        
        if self._pasted_data is not None:
            self.pasted_centroid_rb.setEnabled(True)
            self.pasted_gaussian_rb.setEnabled(True)
            self.pasted_lbl.setEnabled(True)
            self.clear_spectrum_action.setEnabled(True)
        else:
            warn()
        
    def clear_pasted_spectrum(self):
        self._pasted_data = None
        self.pasted_centroid_rb.setEnabled(False)
        self.pasted_gaussian_rb.setEnabled(False)
        self.pasted_lbl.setEnabled(False)
        self.clear_spectrum_action.setEnabled(False)
        self.on_draw()
    
    def on_about(self):
        msg = ''' %s:
        An application to calculate isotopic distribution from chemical formula.
        Copyright (c) 2015-2024 Nicolas Elie
        Skeleton of application from Eli Bendersky (http://eli.thegreenplace.net/2009/01/20/matplotlib-with-pyqt-guis)
        Core of application (molmass) from Christoph Gohlke (http://www.lfd.uci.edu/~gohlke/)
        Icon by Scout on OpenClipart (https://openclipart.org)
        ''' % APP_NAME
        QMessageBox.about(self, 'About %s' % APP_NAME, msg.strip())
        
    def on_radio_resolution_toggled(self):
        self.fwhm_spinbox.setEnabled(self.fwhm_rb.isChecked())
        self.resolution_spinbox.setEnabled(not self.fwhm_rb.isChecked())
        self.on_draw()
        
    def on_show_gaussian(self):
        self.fwhm_rb.setEnabled(self.gaussian_cb.isChecked())
        self.fwhm_spinbox.setEnabled(self.fwhm_rb.isChecked() and self.gaussian_cb.isChecked())
        self.resolution_rb.setEnabled(self.gaussian_cb.isChecked())
        self.resolution_spinbox.setEnabled(self.resolution_rb.isChecked() and self.gaussian_cb.isChecked())
        
        self.on_draw()
        
    def on_mz_digits_changed(self):
        self.ppm_spinbox.setDecimals(self.mz_digits_spinbox.value())
        self.on_draw()
        
    def on_cb_ppm_checked(self):
        self.ppm_spinbox.setEnabled(self.ppm_cb.isChecked())
        self.ppm_lbl.setEnabled(self.ppm_cb.isChecked())
        
    def on_formula_validate(self, *args):        
        try:
            #Get formula from user entry
            text = str(self.formula_cbox.currentText())
        
            #Analyze user entry
            formula = Formula(text)
            
            #Generate spectrum
            spectrum = formula.spectrum()
        except:
            if text != self._last_invalid_formula:
                QMessageBox.warning(self, 'Warning', 'Formula invalid.')
                self._last_invalid_formula = text
            return False
        else:
            self._formula = formula
            self._spectrum = spectrum
            if self.formula_cbox.findText(text) == -1:
                self.formula_cbox.insertItem(0, text)
            self.on_draw()
    
    def on_draw(self):
        ''' Redraws the figure
        '''
        digits = self.mz_digits_spinbox.value()
        
        if self._spectrum is not None and self._formula is not None:
            spectrum = self._spectrum
            formula = self._formula
        else:
            return False

        x, y = np.asarray([(s.mass, s.intensity) for s in spectrum.values()]).T
                
        #Filter values below minimum abundance
        ind = np.where(y>self.minabund_spinbox.value())
        x, y = x[ind], y[ind]
        
        #Save data
        self._data = list(zip(x, y))
        
        # Fill the table
        model = self.table.model()
        model.set_values(np.asarray(list(zip(x, y, y/y.sum()*100.0, y/y[0]*100.0))))
        model.set_mz_digits(self.mz_digits_spinbox.value())
        model.set_abundance_digits(self.abund_digits_spinbox.value())
        self.table.resizeColumnsToContents()
        
        # Clear the axes and redraw the plot anew
        #
        self.axes.clear()
        self.axes.grid(self.grid_cb.isChecked())
        
        self.axes.vlines(x, 0, y, colors=self.centroid_color_bt.color(),
                                  linestyles=self.centroid_color_bt.lineStyle())
        min, max = x.min() - 1, x.max() + 1
        
        if not self.centroid_cb.isChecked():
            self.axes.clear()
            
        if self._pasted_data is not None:
            x_pasted = self._pasted_data[:,0]
            y_pasted = self._pasted_data[:,1]
            if self.pasted_centroid_rb.isChecked():
                self.axes.vlines(x_pasted, 0, y_pasted, colors=self.pasted_color_bt.color(),
                                 linestyles=self.pasted_color_bt.lineStyle())
            else:
                self.axes.plot(x_pasted, y_pasted, color=self.pasted_color_bt.color(),
                               linestyle=self.pasted_color_bt.lineStyle(),
                               marker=self.pasted_color_bt.lineMarker())
        
        if self.gaussian_cb.isChecked():
            if self.fwhm_rb.isChecked():
                gaussian_parameter = {'fwhm': self.fwhm_spinbox.value()}
            elif self.resolution_rb.isChecked():
                gaussian_parameter = {'resolution': self.resolution_spinbox.value()}
            
            range = int(max - min)
            charge = formula.charge if formula.charge != 0 else 1
            x_gaussian = np.linspace(min, max, 500*range*abs(charge))
            y_gaussian_total = None
            for x, y in self._data:
                fwhm = gaussian_parameter.get('fwhm', None)
                if fwhm is None:
                    try:
                        fwhm = x / gaussian_parameter.get('resolution', 0)
                    except ZeroDivisionError:
                        fwhm = DEFAULT_FWHM
                sigma = fwhm / (2*np.sqrt(2*np.log(2)))

                y_gaussian = normpdf(x_gaussian, x, sigma)
                if y_gaussian.max() > 0:
                    y_gaussian = y_gaussian/y_gaussian.max()*y
                    
                if y_gaussian_total is None:
                    y_gaussian_total = y_gaussian
                else:
                    y_gaussian_total += y_gaussian
            if y_gaussian_total.max() > 0:
                y_gaussian_total = y_gaussian_total/y_gaussian_total.max()*100.0
            self.axes.plot(x_gaussian, y_gaussian_total, color=self.gaussian_color_bt.color(),
                           linestyle=self.gaussian_color_bt.lineStyle(),
                           marker=self.gaussian_color_bt.lineMarker())
                           
        if self._pasted_data is None:
            self.axes.set_xbound(min, max)
        
        if self.annotate_cb.isChecked():
            for i,j in self._data:
                if j>=ANNOTATE_THRESHOLD:
                    if j>=85:
                        self.axes.annotate('%.*f' % (digits, i), xy=(i,j),
                                            xytext=(-4.0,-20.0), textcoords='offset points',
                                            rotation='vertical', annotation_clip=False)
                    else:
                        self.axes.annotate('%.*f' % (digits, i), xy=(i,j),
                                            xytext=(-4.0,20+digits*8.0),
                                            textcoords='offset points',
                                            rotation='vertical', annotation_clip=False)
        
        self.axes.spines['top'].set_visible(False)
        self.axes.spines['right'].set_visible(False)
        self.axes.get_xaxis().tick_bottom()
        self.axes.get_yaxis().tick_left()
        
        self.axes.xaxis.set_label_text(X_AXIS_LABEL, style=X_AXIS_LABEL_STYLE, weight='bold')
        
        self.axes.yaxis.set_major_locator(MultipleLocator(base=10.0))
        self.axes.yaxis.set_minor_locator(MultipleLocator(base=5.0))
        self.axes.yaxis.set_label_text(Y_AXIS_LABEL, style=Y_AXIS_LABEL_STYLE, weight='bold')
        
        charge_text = str(abs(formula.charge)) if (abs(formula.charge) > 1) else ''
        formula_mathtext = str(formula.formula)
        formula_mathtext = SUPERSCRIPT_CHARGE_RE.sub(r'^{\1}', formula_mathtext)
        formula_mathtext = SUBSCRIPT_NUMBER_RE.sub(r'_{\1}', formula_mathtext)
        self.axes.set_title(r'$%s$ (%.*f)' % (formula_mathtext, digits, spectrum.peak.mass))
        
        if self.ppm_cb.isChecked() and abs(self.ppm_spinbox.value()-spectrum.peak.mass)<1.0:
            expected_mass = Decimal('%.*f' % (digits, spectrum.peak.mass))
            experimental_mass = Decimal('%.*f' % (digits, self.ppm_spinbox.value()))
            
            error_ppm = (experimental_mass-expected_mass)*Decimal('1e6')/expected_mass
            self.ppm_lbl.setText('%.2f ppm' % error_ppm)
        
        self.axes.set_ybound(0, 100)
        self.fig.set_facecolor('w')
        self.fig.tight_layout()
        self.canvas.draw()
    
    def create_main_frame(self):
        self.main_frame = QWidget()

        self.fig = Figure()
        self.canvas = FigureCanvas(self.fig)
        self.canvas.setParent(self.main_frame)
        
        # Since we have only one plot, we can use add_axes 
        # instead of add_subplot, but then the subplot
        # configuration tool in the navigation toolbar wouldn't
        # work.
        #
        self.axes = self.fig.add_subplot(111)
        
        # Create the navigation toolbar, tied to the canvas
        #
        mpl_toolbar = NavigationToolbar(self.canvas, self.main_frame)
        
        # Create the table view
        self.table = QTableView()
        self.table.setModel(MZTableModel())
        self.table.setSortingEnabled(True)
        
        # Other GUI controls
        # 
        self.formula_cbox = FormulaComboBox()
        self.formula_cbox.addItems(self.options['history'])
        self.formula_cbox.lineEdit().editingFinished.connect(self.on_formula_validate)
        self.formula_cbox.currentIndexChanged.connect(self.on_formula_validate)        
        
        self.draw_button = QPushButton('&Draw')
        self.draw_button.setIcon(QIcon(DRAW_ICON))
        self.draw_button.clicked.connect(self.on_formula_validate)
        
        self.grid_cb = QCheckBox('Show &Grid')
        self.grid_cb.setChecked(self.options['show_grid'])
        self.grid_cb.stateChanged.connect(self.on_draw)
        
        self.annotate_cb = QCheckBox('Show &Annotations')
        self.annotate_cb.setChecked(self.options['show_annotations'])
        self.annotate_cb.stateChanged.connect(self.on_draw)

        self.centroid_cb = QCheckBox('Show &Centroid')
        self.centroid_cb.setChecked(self.options['show_centroid'])
        self.centroid_cb.stateChanged.connect(self.on_draw)
        
        self.gaussian_cb = QCheckBox('Show &Gaussian')
        self.gaussian_cb.setChecked(self.options['show_gaussian'])
        self.gaussian_cb.stateChanged.connect(self.on_show_gaussian)
        
        gaussian_group = QButtonGroup(self.main_frame)
        
        self.fwhm_rb = QRadioButton('Constant &FWHM')
        self.fwhm_rb.setChecked(self.options['gaussian_use_constant_fwhm'])
        self.fwhm_rb.setEnabled(self.options['show_gaussian'])
        gaussian_group.addButton(self.fwhm_rb)
        self.fwhm_rb.toggled.connect(self.on_radio_resolution_toggled)

        self.fwhm_spinbox = QDoubleSpinBox()
        self.fwhm_spinbox.setRange(MINIMUM_FWHM, MAXIMUM_FWHM)
        self.fwhm_spinbox.setSingleStep(0.05)
        self.fwhm_spinbox.setValue(self.options['gaussian_constant_fwhm'])
        self.fwhm_spinbox.setEnabled(self.options['gaussian_use_constant_fwhm'] and self.options['show_gaussian'])
        self.fwhm_spinbox.valueChanged.connect(self.on_draw)
        
        self.resolution_rb = QRadioButton('Constant &Resolution')
        self.resolution_rb.setChecked(self.options['gaussian_use_constant_resolution'])
        self.resolution_rb.setEnabled(self.options['show_gaussian'])
        gaussian_group.addButton(self.resolution_rb)
        self.resolution_rb.toggled.connect(self.on_radio_resolution_toggled)
        
        self.resolution_spinbox = QSpinBox()
        self.resolution_spinbox.setRange(MINIMUM_RESOLUTION, MAXIMUM_RESOLUTION)
        self.resolution_spinbox.setSingleStep(1000)
        self.resolution_spinbox.setValue(self.options['gaussian_constant_resolution'])
        self.resolution_spinbox.setEnabled(self.options['gaussian_use_constant_resolution'] and self.options['show_gaussian'])
        self.resolution_spinbox.valueChanged.connect(self.on_draw)
        
        minabund = QLabel('Minimum abundance:')
        #minabund.setFixedSize(minabund.minimumSizeHint())
        self.minabund_spinbox = QDoubleSpinBox()
        self.minabund_spinbox.setRange(0.0, 100.0)
        self.minabund_spinbox.setSingleStep(0.1)
        self.minabund_spinbox.setSuffix('%')
        self.minabund_spinbox.setValue(self.options['minimum_abundance'])
        self.minabund_spinbox.valueChanged.connect(self.on_draw)
        
        mz_digits = QLabel('<i>m/z</i> digits:')
        #mz_digits.setFixedSize(mz_digits.minimumSizeHint())
        self.mz_digits_spinbox = QSpinBox()
        self.mz_digits_spinbox.setRange(0, 10)
        self.mz_digits_spinbox.setSingleStep(1)
        self.mz_digits_spinbox.setValue(self.options['mz_digits'])
        self.mz_digits_spinbox.valueChanged.connect(self.on_mz_digits_changed)
        
        abund_digits = QLabel('Abundance digits:')
        #abund_digits.setFixedSize(abund_digits.minimumSizeHint())
        self.abund_digits_spinbox = QSpinBox()
        self.abund_digits_spinbox.setRange(0, 10)
        self.abund_digits_spinbox.setSingleStep(1)
        self.abund_digits_spinbox.setValue(self.options['abundance_digits'])
        self.abund_digits_spinbox.valueChanged.connect(self.on_draw)
        
        pasted_group = QButtonGroup(self.main_frame)
        self.pasted_lbl = QLabel('Type of pasted data:')
        self.pasted_lbl.setEnabled(False)
        self.pasted_centroid_rb = QRadioButton('&Centroid')
        self.pasted_centroid_rb.setChecked(True)
        self.pasted_centroid_rb.setEnabled(False)
        self.pasted_centroid_rb.toggled.connect(self.on_draw)
        pasted_group.addButton(self.pasted_centroid_rb)
        self.pasted_gaussian_rb = QRadioButton('&Gaussian')
        self.pasted_gaussian_rb.setEnabled(False)
        self.pasted_gaussian_rb.toggled.connect(self.on_draw)
        pasted_group.addButton(self.pasted_gaussian_rb)
        
        self.ppm_cb = QCheckBox('Compare to:')
        self.ppm_cb.setChecked(False)
        self.ppm_cb.stateChanged.connect(self.on_cb_ppm_checked)
        
        self.ppm_spinbox = QDoubleSpinBox()
        self.ppm_spinbox.setEnabled(False)
        self.ppm_spinbox.setDecimals(DEFAULT_MZ_DIGITS)
        self.ppm_spinbox.setSingleStep(0.1)
        self.ppm_spinbox.setRange(0, sys.float_info.max)
        self.ppm_spinbox.setPrefix('m/z ')
        self.ppm_spinbox.valueChanged.connect(self.on_draw)
        self.ppm_lbl = QLabel()
        
        self.centroid_color_bt = MatplotLibStyleButton(self.options['centroid_color'], DEFAULT_CENTROID_COLOR,
                                                        self.options['centroid_linestyle'], DEFAULT_CENTROID_STYLE)
        self.centroid_color_bt.colorChanged.connect(self.on_draw)
        self.centroid_color_bt.lineStyleChanged.connect(self.on_draw)
        self.centroid_color_bt.markerChanged.connect(self.on_draw)
        self.gaussian_color_bt = MatplotLibStyleButton(self.options['gaussian_color'], DEFAULT_GAUSSIAN_COLOR,
                                                        self.options['gaussian_linestyle'], DEFAULT_GAUSSIAN_STYLE,
                                                        self.options['gaussian_marker'], DEFAULT_GAUSSIAN_MARKER)
        self.gaussian_color_bt.colorChanged.connect(self.on_draw)
        self.gaussian_color_bt.lineStyleChanged.connect(self.on_draw)
        self.gaussian_color_bt.markerChanged.connect(self.on_draw)
        self.pasted_color_bt = MatplotLibStyleButton(self.options['pasted_color'], DEFAULT_PASTED_COLOR,
                                                      self.options['pasted_linestyle'], DEFAULT_PASTED_STYLE,
                                                      self.options['pasted_marker'], DEFAULT_PASTED_MARKER)
        self.pasted_color_bt.colorChanged.connect(self.on_draw)
        self.pasted_color_bt.lineStyleChanged.connect(self.on_draw)
        self.pasted_color_bt.markerChanged.connect(self.on_draw)
        
        #
        # Layout with box sizers
        # 
        hbox = QHBoxLayout()
        for w in [self.formula_cbox, self.draw_button, self.grid_cb, self.annotate_cb,
                  self.centroid_cb, self.gaussian_cb, self.fwhm_rb, self.fwhm_spinbox,
                  self.resolution_rb, self.resolution_spinbox]:
            hbox.addWidget(w)
            hbox.setAlignment(w, Qt.AlignVCenter)
        hbox.addStretch(0)
        
        hbox2 = QHBoxLayout()
        for w in [minabund, self.minabund_spinbox, mz_digits, self.mz_digits_spinbox,
                  abund_digits, self.abund_digits_spinbox, self.pasted_lbl,
                  self.pasted_centroid_rb, self.pasted_gaussian_rb, self.ppm_cb,
                  self.ppm_spinbox, self.ppm_lbl, self.centroid_color_bt, self.gaussian_color_bt,
                  self.pasted_color_bt]:
            hbox2.addWidget(w)
            hbox2.setAlignment(w, Qt.AlignVCenter)
        hbox2.addStretch(0)
        
        vbox = QVBoxLayout()
        vbox.addLayout(hbox)
        vbox.addLayout(hbox2)
        vbox.addWidget(mpl_toolbar)
        
        splitter = QSplitter()
        splitter.addWidget(self.canvas)
        splitter.addWidget(self.table)
        splitter.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        vbox.addWidget(splitter)
        
        self.main_frame.setLayout(vbox)
        self.setCentralWidget(self.main_frame)
        
    def create_menu(self):        
        self.file_menu = self.menuBar().addMenu('&File')
        
        save_plot_action = self.create_action('&Save plot',
            shortcut='Ctrl+S', slot=self.save_plot, 
            tip='Save the plot')
        quit_action = self.create_action('&Quit', slot=self.close, 
            shortcut='Ctrl+Q', tip='Close the application')
        
        self.add_actions(self.file_menu, 
            (save_plot_action, None, quit_action))
            
        self.edit_menu = self.menuBar().addMenu('&Edit')
        copy_spectrum_action = self.create_action('&Copy spectrum',
            shortcut='Ctrl+Shift+C', slot=self.copy_spectrum,
            tip='Copy spectrum data to the clipboard')
        paste_spectrum_action = self.create_action('&Paste spectrum',
            shortcut='Ctrl+Shift+V', slot=self.paste_spectrum,
            tip='Paste spectrum from the clipboard')
        self.clear_spectrum_action = self.create_action('C&lear spectrum',
            shortcut='Ctrl+Shift+L', slot=self.clear_pasted_spectrum,
            tip='Remove pasted spectrum')
        self.clear_spectrum_action.setEnabled(False)
            
        self.add_actions(self.edit_menu,
            (copy_spectrum_action, None, paste_spectrum_action, self.clear_spectrum_action))
        
        self.help_menu = self.menuBar().addMenu('&Help')
        about_action = self.create_action('&About', 
            shortcut='F1', slot=self.on_about, 
            tip='About the demo')
        
        self.add_actions(self.help_menu, (about_action,))

    def add_actions(self, target, actions):
        for action in actions:
            if action is None:
                target.addSeparator()
            else:
                target.addAction(action)

    def create_action(self, text, slot=None, shortcut=None, 
                      icon=None, tip=None, checkable=False):
        action = QAction(text, self)
        if icon is not None:
            action.setIcon(QIcon(':/%s.png' % icon))
        if shortcut is not None:
            action.setShortcutContext(Qt.WidgetShortcut)
            action.setShortcut(shortcut)
        if tip is not None:
            action.setToolTip(tip)
            action.setStatusTip(tip)
        if slot is not None:
            action.triggered.connect(slot)
        if checkable:
            action.setCheckable(True)
        return action

class FormulaComboBox(QComboBox):
    def focusOutEvent (self, e):
        pass
        
    def __init__(self, parent=None):
        super().__init__(parent)
        
        self.setEditable(True)
        self.setMaxCount(MAX_FORMULAE)
        self.setMinimumWidth(200)
        
        #Control insertion of formula in the combobox
        self.setInsertPolicy(QComboBox.NoInsert)

        #Case sensitive completer
        completer = QCompleter(self)
        completer.setCaseSensitivity(Qt.CaseSensitive)
        self.setCompleter(completer)
        
class MZTableModel(QAbstractTableModel):
    _headers = ['m/z', 'Abund.\n(% largest)', 'Abund.\n(% sum)', 'Abund.\n(% first)']
    
    def __init__(self, data=None, mz_digits=DEFAULT_MZ_DIGITS,
                abund_digits=DEFAULT_ABUNDANCE_DIGITS,
                parent=None, *args):
        super().__init__(parent, *args)
        self._data = data
        self._mz_digits = mz_digits
        self._abund_digits = abund_digits
    
    def rowCount(self, parent):
        if self._data is not None:
            return len(self._data)
        return 0

    def columnCount(self, parent):
        if self._data is not None and len(self._data) > 0: 
            return len(self._data[0])
        return 0
    
    def headerData(self, section, orientation, role):
        if orientation == Qt.Horizontal and role == Qt.DisplayRole:
            return self._headers[section]
        return QAbstractTableModel.headerData(self, section, orientation, role)
        
    def data(self, index, role):
        if not index.isValid():
            return None
        elif role != Qt.DisplayRole:
            return None
        if index.column() == 0:
            return '%.*f' % (self._mz_digits, self._data[index.row()][index.column()])
        else:
            return '%.*f' % (self._abund_digits, self._data[index.row()][index.column()])
 
    def sort(self, column, order):
        """sort table by given column number col"""
        if self._data is not None:
            self.layoutAboutToBeChanged.emit()
            if order == Qt.DescendingOrder:
                sort_arr = np.argsort(self._data[:, column])[::-1]
            else:
                sort_arr = np.argsort(self._data[:,column])
            self._data = self._data[sort_arr]
            self.layoutChanged.emit()
 
    def set_values(self, data):
        self.layoutAboutToBeChanged.emit()
        self._data = data
        self.layoutChanged.emit()
    
    def set_mz_digits(self, mz_digits):
        self.layoutAboutToBeChanged.emit()
        self._mz_digits = mz_digits
        self.layoutChanged.emit()
        
    def set_abundance_digits(self, abund_digits):
        self.layoutAboutToBeChanged.emit()
        self._abund_digits = abund_digits
        self.layoutChanged.emit()
        
#http://martinfitzpatrick.name/article/qcolorbutton-a-color-selector-tool-for-pyqt/
class MatplotLibStyleButton(QPushButton):
    '''
    Custom Qt Widget to show a chosen color.

    Left-clicking the button shows the color-chooser, while
    right-clicking resets the color to None (no-color).    
    '''
    MATPLOTLIB_COLORS = {'b': '#0000FF', 'g': '#008000', 'r': '#FF0000', 'c': '#00C0C0',
                         'm': '#C000C0', 'y': '#C0C000', 'k': '#000000', 'w': '#FFFFFF'}
    colorChanged = Signal(object)
    lineStyleChanged = Signal(object)
    markerChanged = Signal(object)
    styleSheetModel = """border: 2px solid #8f8f91;
                         border-radius: 6px;
                         background-color: qlineargradient(x1: 0, y1: 0, x2: 0, y2: 1,
                                       stop: 0 %s, stop: 1 #dadbde);"""
    lineStyles = sorted([x for x in matplotlib.lines.lineStyles.keys() if x not in [' ', '', 'None', None]],
                         key=lambda x: str(x))
    lineMarkers = sorted([x for x in matplotlib.lines.lineMarkers.keys() if x not in [' ', 'None', None, 0, 5, 6, 7, '3', '2', '4', '8', '1']],
                         key=lambda x: str(x))

    def __init__(self, color, defaultcolor, linestyle, defaultlinestyle, 
            linemarker=None, defaultlinemarker=None, *args, **kwargs):
        super().__init__(*args, **kwargs)

        self._color = color
        self._defaultcolor = defaultcolor
        self._linestyle = linestyle
        self._defaultlinestyle = defaultlinestyle
        self._lineMarker = linemarker
        self._defaultlinemarker = defaultlinemarker
        self._hasLineMarker = (linemarker is not None and defaultlinemarker is not None)
        self.setColor(color)
        self.setMaximumWidth(32)
        
        menu = QMenu()
        menu.addAction('Select color...', self.onColorPicker)
        submenu = menu.addMenu('Line style')
        self._lineStyleActions = []
        for style in self.lineStyles:
            action = submenu.addAction(style, lambda arg=style: self.setLineStyle(arg))
            action.setCheckable(True)
            if style == self._linestyle:
                action.setChecked(True)
            self._lineStyleActions.append(action)
        
        if self._hasLineMarker:
            submenu = menu.addMenu('Line Marker')
            self._lineMarkerActions = []
            for marker in self.lineMarkers:
                action = submenu.addAction(str(marker), lambda arg=marker: self.setLineMarker(arg))
                action.setCheckable(True)
                if style == self._lineMarker:
                    action.setChecked(True)
                self._lineMarkerActions.append(action)
            
        self._menu = menu
        self.setMenu(menu)
        
    def setLineStyle(self, style):
        for a in self._lineStyleActions:
            if a.text() == style:
                a.setChecked(True)
            else:
                a.setChecked(False)
                
        if style != self._linestyle:
            self._linestyle = style
            self.lineStyleChanged.emit(style)
            
    def setLineMarker(self, marker):
        if not self._hasLineMarker:
            return False
        
        for a in self._lineMarkerActions:
            if a.text() == marker:
                a.setChecked(True)
            else:
                a.setChecked(False)
                
        if marker != self._lineMarker:
            self._lineMarker = marker
            self.markerChanged.emit(marker)

    def setColor(self, color):
        if color in self.MATPLOTLIB_COLORS.keys():
            color = self.MATPLOTLIB_COLORS[color]
        
        if color != self._color:
            self._color = color
            self.colorChanged.emit(color)

        if self._color:
            self.setStyleSheet(self.styleSheetModel % self._color)
        else:
            self.setStyleSheet("")

    def color(self):
        if type(self._color) == str:
            return str(self._color)
        else:
            return self._color
            
    def lineStyle(self):
        return self._linestyle

    def lineMarker(self):
        if self._hasLineMarker:
            return str(self._lineMarker)
        else:
            return False

    def onColorPicker(self):
        '''
        Show color-picker dialog to select color.

        Qt will use the native dialog by default.

        '''
        dlg = QColorDialog(self.parent())
        if self._color:
            dlg.setCurrentColor(QColor(self._color))

        if dlg.exec():
            self.setColor(dlg.currentColor().name())

    def mousePressEvent(self, e):
        if e.button() == Qt.RightButton:
            self.setColor(self._defaultcolor)
            self.setLineStyle(self._defaultlinestyle)
            self.setLineMarker(self._defaultlinemarker)

        return super().mousePressEvent(e)

if __name__ == '__main__':
    app = QApplication(sys.argv)
    form = AppForm()
    form.show()
    app.exec()
