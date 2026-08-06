import base64
import binascii
import hashlib
import html
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import List, Optional, Set, Tuple

import tkinter as tk
from tkinter import filedialog, messagebox, ttk


APP_TITLE = "HTML Image Extractor"


# Намира изображения от типа:
# data:image/png;base64,iVBORw0KGgo...
#
# Работи както в <img src="...">, така и в CSS background-image.
DATA_IMAGE_PATTERN = re.compile(
    r"data:image/"
    r"(?P<mime>[a-zA-Z0-9.+_-]+)"
    r"(?:;[^,]*)?"
    r";base64,"
    r"(?P<data>[a-zA-Z0-9+/=\s]+)",
    re.IGNORECASE,
)


EXTENSIONS = {
    "png": "png",
    "jpeg": "jpg",
    "jpg": "jpg",
    "gif": "gif",
    "webp": "webp",
    "bmp": "bmp",
    "svg+xml": "svg",
    "x-icon": "ico",
    "vnd.microsoft.icon": "ico",
    "tiff": "tiff",
    "avif": "avif",
}


def read_html_file(file_path):
    # Опитва няколко често срещани кодировки.
    encodings = [
        "utf-8-sig",
        "utf-8",
        "windows-1251",
        "windows-1252",
        "latin-1",
    ]

    for encoding in encodings:
        try:
            with open(file_path, "r", encoding=encoding) as file:
                return file.read()
        except UnicodeDecodeError:
            continue

    with open(file_path, "r", encoding="utf-8", errors="replace") as file:
        return file.read()


def normalize_base64(encoded_data):
    encoded_data = html.unescape(encoded_data)
    return re.sub(r"\s+", "", encoded_data)


def get_extension(mime_subtype):
    mime_subtype = mime_subtype.lower().strip()
    return EXTENSIONS.get(mime_subtype, "bin")


def create_output_directory(html_file):
    """
    report.html -> report_images

    Ако папката вече съществува:
    report_images_2
    report_images_3
    """
    base_directory = html_file.parent / "{}_images".format(html_file.stem)

    if not base_directory.exists():
        base_directory.mkdir(parents=True)
        return base_directory

    counter = 2

    while True:
        directory = html_file.parent / "{}_images_{}".format(
            html_file.stem,
            counter,
        )

        if not directory.exists():
            directory.mkdir(parents=True)
            return directory

        counter += 1


def decode_image(encoded_data):
    """
    Декодира Base64 съдържанието.

    Първо опитва строг режим, след това добавя липсващото
    Base64 padding, ако е необходимо.
    """
    encoded_data = normalize_base64(encoded_data)

    try:
        return base64.b64decode(encoded_data, validate=True)
    except (binascii.Error, ValueError):
        pass

    missing_padding = len(encoded_data) % 4

    if missing_padding:
        encoded_data += "=" * (4 - missing_padding)

    try:
        return base64.b64decode(encoded_data)
    except (binascii.Error, ValueError):
        return None


def extract_images(html_file):
    """
    Извлича Base64 изображенията от един HTML файл.

    Връща:
    saved_count, duplicate_count, invalid_count, output_directory
    """
    html_content = read_html_file(html_file)
    html_content = html.unescape(html_content)

    matches = list(DATA_IMAGE_PATTERN.finditer(html_content))

    if not matches:
        return 0, 0, 0, None

    output_directory = create_output_directory(html_file)

    saved_count = 0
    duplicate_count = 0
    invalid_count = 0
    image_hashes = set()

    for match in matches:
        mime_subtype = match.group("mime")
        encoded_data = match.group("data")

        image_bytes = decode_image(encoded_data)

        if not image_bytes:
            invalid_count += 1
            continue

        image_hash = hashlib.sha256(image_bytes).hexdigest()

        if image_hash in image_hashes:
            duplicate_count += 1
            continue

        image_hashes.add(image_hash)

        extension = get_extension(mime_subtype)
        saved_count += 1

        output_file = output_directory / "image_{:03d}.{}".format(
            saved_count,
            extension,
        )

        with open(output_file, "wb") as file:
            file.write(image_bytes)

    if saved_count == 0:
        try:
            output_directory.rmdir()
        except OSError:
            pass

        return 0, duplicate_count, invalid_count, None

    return (
        saved_count,
        duplicate_count,
        invalid_count,
        output_directory,
    )


def open_directory(directory):
    try:
        if sys.platform.startswith("win"):
            os.startfile(str(directory))
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(directory)])
        else:
            subprocess.Popen(["xdg-open", str(directory)])
    except Exception as error:
        messagebox.showerror(
            APP_TITLE,
            "Папката не може да бъде отворена:\n{}".format(error),
        )


class HTMLImageExtractorApp:
    def __init__(self, root):
        self.root = root
        self.last_output_directory = None

        self.root.title(APP_TITLE)
        self.root.geometry("680x500")
        self.root.minsize(580, 420)

        self.build_interface()

    def build_interface(self):
        main_frame = ttk.Frame(self.root, padding=24)
        main_frame.pack(fill="both", expand=True)

        title_label = ttk.Label(
            main_frame,
            text="Извличане на снимки от HTML",
            font=("Segoe UI", 18, "bold"),
        )
        title_label.pack(pady=(0, 8))

        description_label = ttk.Label(
            main_frame,
            text=(
                "Избери един или повече HTML файлове.\n"
                "Вградените Base64 снимки ще бъдат записани "
                "в нова папка до HTML файла."
            ),
            justify="center",
        )
        description_label.pack(pady=(0, 20))

        self.select_button = ttk.Button(
            main_frame,
            text="Избери HTML файлове",
            command=self.select_files,
        )
        self.select_button.pack(ipadx=24, ipady=10, pady=(0, 16))

        self.progress = ttk.Progressbar(
            main_frame,
            mode="determinate",
        )
        self.progress.pack(fill="x", pady=(0, 14))

        log_frame = ttk.LabelFrame(
            main_frame,
            text="Резултат",
            padding=10,
        )
        log_frame.pack(fill="both", expand=True)

        self.log_text = tk.Text(
            log_frame,
            height=12,
            wrap="word",
            state="disabled",
        )
        self.log_text.pack(side="left", fill="both", expand=True)

        scrollbar = ttk.Scrollbar(
            log_frame,
            orient="vertical",
            command=self.log_text.yview,
        )
        scrollbar.pack(side="right", fill="y")

        self.log_text.configure(yscrollcommand=scrollbar.set)

        self.open_folder_button = ttk.Button(
            main_frame,
            text="Отвори последната папка",
            command=self.open_last_directory,
            state="disabled",
        )
        self.open_folder_button.pack(pady=(14, 0))

    def add_log(self, message):
        self.log_text.configure(state="normal")
        self.log_text.insert("end", message + "\n")
        self.log_text.see("end")
        self.log_text.configure(state="disabled")
        self.root.update_idletasks()

    def clear_log(self):
        self.log_text.configure(state="normal")
        self.log_text.delete("1.0", "end")
        self.log_text.configure(state="disabled")

    def select_files(self):
        selected_files = filedialog.askopenfilenames(
            title="Избери HTML файлове",
            filetypes=[
                ("HTML файлове", "*.html *.htm"),
                ("Всички файлове", "*.*"),
            ],
        )

        if not selected_files:
            return

        files = [Path(file_path) for file_path in selected_files]
        self.process_files(files)

    def process_files(self, files):
        self.clear_log()

        self.select_button.configure(state="disabled")
        self.open_folder_button.configure(state="disabled")
        self.last_output_directory = None

        self.progress.configure(
            maximum=len(files),
            value=0,
        )

        total_images = 0
        successful_files = 0
        files_without_images = 0
        failed_files = 0

        try:
            for index, html_file in enumerate(files, start=1):
                self.add_log("Обработва се: {}".format(html_file.name))

                try:
                    (
                        saved_count,
                        duplicate_count,
                        invalid_count,
                        output_directory,
                    ) = extract_images(html_file)

                    if saved_count > 0:
                        successful_files += 1
                        total_images += saved_count
                        self.last_output_directory = output_directory

                        self.add_log(
                            "  ✓ Записани снимки: {}".format(saved_count)
                        )

                        if duplicate_count:
                            self.add_log(
                                "  • Пропуснати дубликати: {}".format(
                                    duplicate_count
                                )
                            )

                        if invalid_count:
                            self.add_log(
                                "  • Невалидни изображения: {}".format(
                                    invalid_count
                                )
                            )

                        self.add_log(
                            "  • Папка: {}".format(output_directory)
                        )
                    else:
                        files_without_images += 1
                        self.add_log(
                            "  Няма намерени валидни Base64 снимки."
                        )

                        if invalid_count:
                            self.add_log(
                                "  • Невалидни изображения: {}".format(
                                    invalid_count
                                )
                            )

                except PermissionError:
                    failed_files += 1
                    self.add_log(
                        "  ✗ Няма разрешение за запис в тази папка."
                    )

                except OSError as error:
                    failed_files += 1
                    self.add_log(
                        "  ✗ Файлова грешка: {}".format(error)
                    )

                except Exception as error:
                    failed_files += 1
                    self.add_log(
                        "  ✗ Неочаквана грешка: {}".format(error)
                    )

                self.add_log("")
                self.progress.configure(value=index)
                self.root.update_idletasks()

        finally:
            self.select_button.configure(state="normal")

        if self.last_output_directory is not None:
            self.open_folder_button.configure(state="normal")

        summary = (
            "Обработката приключи.\n\n"
            "Извлечени снимки: {}\n"
            "Успешни HTML файлове: {}\n"
            "Файлове без Base64 снимки: {}\n"
            "Файлове с грешка: {}"
        ).format(
            total_images,
            successful_files,
            files_without_images,
            failed_files,
        )

        messagebox.showinfo(APP_TITLE, summary)

    def open_last_directory(self):
        if self.last_output_directory is not None:
            open_directory(self.last_output_directory)


def main():
    root = tk.Tk()

    try:
        if sys.platform.startswith("win"):
            ttk.Style().theme_use("vista")
    except tk.TclError:
        pass

    HTMLImageExtractorApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()