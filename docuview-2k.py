# 这是原文件
import os
import re

script_dir = os.path.dirname(os.path.abspath(__file__))

# 创建所需的 static 目录
static_dir = os.path.join(script_dir, "static")
if not os.path.exists(static_dir):
    os.makedirs(static_dir, exist_ok=True)

# 设置环境变量
os.environ["FITZ_STATIC_PATH"] = static_dir

import tkinter as tk
from tkinter import ttk, scrolledtext, messagebox, filedialog, font, Menu, simpledialog

import sys
import datetime
import math
import base64
import json
import markdown
import fitz
from PIL import Image, ImageTk
import threading
import time
import io
import contextlib

class EnhancedTextViewer:
    def __init__(self, root):
        self.root = root
        self.root.title("分类查看器")
        self.root.geometry("1920x1080")
        self.root.configure(bg="#f0f2f5")
        
        # 设置高DPI支持
        self.set_dpi_aware()
        
        # 当前文件路径
        self.current_file_path = None
        self.content_modified_flag = False
        
        # PDF相关属性
        self.current_pdf = None
        self.current_pdf_page = 0
        self.pdf_images = []  # 存储所有页面的图像引用
        self.pdf_scale = 1.0  # PDF显示缩放比例
        self.pdf_page_var = tk.StringVar()  # 初始化PDF页码变量
        
        # 分类内容
        self.categories = {
            "Python": "Python是一种高级编程语言，以其简洁性和可读性而闻名。\n\n常用功能：\n1. 数据分析\n2. 网络爬虫\n3. 机器学习\n4. Web开发",
            "Conda": "Conda是一个开源的包管理系统和环境管理系统。\n\n主要功能：\n1. 包管理\n2. 环境管理\n3. 跨平台支持\n4. 多种语言支持",
            "Win11使用": "Windows 11是微软推出的最新操作系统。\n\n使用技巧：\n1. 虚拟桌面\n2. 窗口布局\n3. 触摸手势\n4. 任务栏自定义",
            "C++": "C++是一种高效的系统级编程语言。\n\n核心特性：\n1. 面向对象\n2. 模板编程\n3. 内存管理\n4. 高性能计算"
        }
        
        # 自动导入的文件
        self.imported_files = {}
        
        # 代码片段收藏
        self.snippets = {}
        self.load_snippets()  # 加载保存的代码片段
        
        # 笔记功能相关属性
        self.notes = {}  # 存储笔记 {id: {title, content, created_at, updated_at}}
        self.next_note_id = 1  # 下一个笔记ID
        self.current_note_id = None  # 当前打开的笔记ID
        self.notes_dir = os.path.join(os.path.dirname(os.path.abspath(__file__)), "notes")
        os.makedirs(self.notes_dir, exist_ok=True)  # 修复这里：使用os.makedirs而不是os.maked
        self.load_notes()  # 加载保存的笔记

        # 字数统计变量 - 在创建主页之前初始化
        self.word_count_var = tk.StringVar()

        # 创建菜单
        self.create_menu()
        
        # 创建主框架
        self.main_frame = tk.Frame(self.root, bg="#f0f2f5", bd=0, highlightthickness=0)
        self.main_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        # 创建整体布局框架（左侧导航栏 + 右侧内容区）
        self.content_frame = tk.Frame(self.main_frame, bg="#f0f2f5")
        self.content_frame.pack(fill=tk.BOTH, expand=True)
        
        # 创建左侧导航栏
        self.create_navigation_panel()
        
        # 创建右侧内容区域容器
        self.right_content = tk.Frame(self.content_frame, bg="#f0f2f5")
        self.right_content.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(10, 0))
        
        # 创建标题和工具栏
        self.create_header()
        
        # 创建查看区域容器
        self.viewer_container = tk.Frame(self.right_content, bg="#f0f2f5")
        self.viewer_container.pack(fill=tk.BOTH, expand=True)

        # 创建全局输出面板（独立于查看器）
        self.create_global_output_panel()


        
        # 创建欢迎页面
        self.create_home_page()
        
        # 创建文本查看器（初始隐藏）
        self.create_text_viewer()
        
        # 创建PDF查看器（初始隐藏）
        self.create_pdf_viewer()
        
        # 绑定事件
        self.bind_events()
        
        # 创建自定义标签
        self.create_tags()
        
        # 设置字体（支持高分辨率）
        self.set_font()
        
        # 启动时间更新
        self.update_time()
        
        # 扫描并导入文件（包括记忆的文件）
        self.scan_and_import_files()
        
        # 自动保存设置
        self.auto_save_enabled = True
        self.auto_save_interval = 300000  # 5分钟（毫秒）
        self.auto_save_thread = None
        self.auto_save_running = True
        self.auto_save_event = threading.Event()  # 新增
        self.start_auto_save()

    def create_header(self):
        """创建标题和工具栏"""
        # 标题框架
        title_frame = tk.Frame(self.right_content, bg="#f0f2f5")
        title_frame.pack(fill=tk.X, pady=(0, 15))
        
        self.title_label = tk.Label(title_frame, text="分类查看器",
                                  bg="#f0f2f5", fg="#2c3e50", 
                                  font=("Segoe UI", 18, "bold"))
        self.title_label.pack(side=tk.LEFT)
        
        # 工具栏
        toolbar = tk.Frame(self.right_content, bg="#f0f2f5")
        toolbar.pack(fill=tk.X, pady=(0, 15))
        
        # 工具按钮
        tool_btn_style = {"bg": "#3498db", "fg": "white", "bd": 0, 
                         "padx": 12, "pady": 6, "relief": "flat"}
        
        # 导入按钮
        import_btn = tk.Button(toolbar, text="📥 导入文件", command=self.import_file, **tool_btn_style)
        import_btn.pack(side=tk.LEFT, padx=5)
        
        # 保存按钮
        save_btn = tk.Button(toolbar, text="💾 保存", command=self.save_file,
                            bg="#2ecc71", fg="white", bd=0, padx=12, pady=6)
        save_btn.pack(side=tk.LEFT, padx=5)
        
        # 新建按钮
        new_btn = tk.Button(toolbar, text="📄 新建", command=self.new_file,
                           bg="#9b59b6", fg="white", bd=0, padx=12, pady=6)
        new_btn.pack(side=tk.LEFT, padx=5)
        
        # 计算器按钮
        calc_btn = tk.Button(toolbar, text="🧮 计算器", command=self.open_calculator,
                            bg="#e67e22", fg="white", bd=0, padx=12, pady=6)
        calc_btn.pack(side=tk.LEFT, padx=5)
        
        # 修改按钮
        modify_btn = tk.Button(toolbar, text="✏ 编辑", command=self.modify_content,
                              bg="#f39c12", fg="white", bd=0, padx=12, pady=6)
        modify_btn.pack(side=tk.LEFT, padx=5)
        
        # 主页按钮
        home_btn = tk.Button(toolbar, text="🏠 主页", command=self.show_home,
                            bg="#34495e", fg="white", bd=0, padx=12, pady=6)
        home_btn.pack(side=tk.LEFT, padx=5)
        
        # 笔记按钮
        note_btn = tk.Button(toolbar, text="📝 笔记", command=self.take_note,
                            bg="#8e44ad", fg="white", bd=0, padx=12, pady=6)
        note_btn.pack(side=tk.LEFT, padx=5)
        
        # 运行代码按钮
        run_btn = tk.Button(toolbar, text="▶️▶ 运行代码", command=self.run_python_code,
                            bg="#27ae60", fg="white", bd=0, padx=12, pady=6)
        run_btn.pack(side=tk.LEFT, padx=5)
        
        # 输出面板控制按钮
        self.output_toggle_btn = tk.Button(toolbar, text="📤 显示输出", command=self.toggle_output_panel,
                            bg="#16a085", fg="white", bd=0, padx=12, pady=6)
        self.output_toggle_btn.pack(side=tk.LEFT, padx=5)
        
        # PDF导航按钮
        self.pdf_nav_frame = tk.Frame(toolbar, bg="#f0f2f5")
        self.pdf_nav_frame.pack(side=tk.RIGHT, padx=10)
        
        # 初始隐藏PDF导航按钮
        self.pdf_nav_frame.pack_forget()
        
        # 时间显示
        self.time_var = tk.StringVar()
        time_label = tk.Label(toolbar, textvariable=self.time_var, bg="#f0f2f5", 
                             font=("Segoe UI", 11), fg="#666")
        time_label.pack(side=tk.RIGHT, padx=10)
        
        # 搜索区域
        search_frame = tk.Frame(toolbar, bg="#f0f2f5")
        search_frame.pack(side=tk.RIGHT, padx=10)
        
        tk.Label(search_frame, text="🔍 搜索:", bg="#f0f2f5", font=("Segoe UI", 11)).pack(side=tk.LEFT)
        self.search_entry = tk.Entry(search_frame, width=30, font=("Segoe UI", 11), 
                                    highlightthickness=1, highlightcolor="#3498db")
        self.search_entry.pack(side=tk.LEFT, padx=5)
        
        search_btn = tk.Button(search_frame, text="查找", command=self.search_text, 
                              bg="#9b59b6", fg="white", bd=0, padx=12, pady=6)
        search_btn.pack(side=tk.LEFT, padx=5)
        
        next_btn = tk.Button(search_frame, text="下一个", command=self.next_result, 
                            bg="#9b59b6", fg="white", bd=0, padx=12, pady=6)
        next_btn.pack(side=tk.LEFT, padx=5)
    
    def create_global_output_panel(self):
        """创建全局输出面板"""
        # 输出面板框架
        self.output_panel_frame = tk.Frame(self.main_frame, bg="#f0f2f5", height=200)
        self.output_panel_frame.pack(fill=tk.BOTH, expand=False, pady=(10, 0))
        
        # 输出面板标题
        output_title_frame = tk.Frame(self.output_panel_frame, bg="#2c3e50", height=30)
        output_title_frame.pack(fill=tk.X)
        
        tk.Label(output_title_frame, text="输出面板", bg="#2c3e50", fg="white", 
                font=("Segoe UI", 12, "bold")).pack(side=tk.LEFT, padx=10)
        
        # 状态标签
        self.run_status_var = tk.StringVar(value="就绪")
        tk.Label(output_title_frame, textvariable=self.run_status_var, bg="#2c3e50", fg="#27ae60",
                font=("Segoe UI", 11)).pack(side=tk.RIGHT, padx=10)
        
        # 控制按钮
        clear_btn = tk.Button(output_title_frame, text="🗑️ 清空", command=self.clear_output,
                             bg="#e74c3c", fg="white", bd=0, padx=8, pady=2)
        clear_btn.pack(side=tk.RIGHT, padx=5)
        
        # 输出内容区域
        output_frame = tk.Frame(self.output_panel_frame, bg="white")
        output_frame.pack(fill=tk.BOTH, expand=True)
        
        self.output_text = scrolledtext.ScrolledText(
            output_frame, wrap=tk.WORD,
            padx=15, pady=10, highlightthickness=0, border=0,
            state="normal", bg="#f8f9fa", fg="#333", font=("Consolas", 12)
        )
        self.output_text.pack(fill=tk.BOTH, expand=True)
        self.output_text.config(state="disabled")  # 初始设置为只读
        
        # 设置初始高度为200像素
        self.output_panel_frame.pack_propagate(False)
        self.output_panel_frame.config(height=200)
        
        # 添加分割条
        self.output_sash = tk.Frame(self.main_frame, bg="#bdc3c7", height=5, cursor="sb_v_double_arrow")
        self.output_sash.pack(fill=tk.X, pady=0)
        self.output_sash.bind("<ButtonPress-1>", self.start_resize_output)
        self.output_sash.bind("<B1-Motion>", self.resize_output)
        
        # 初始显示输出面板
        self.output_panel_visible = True
    
    def toggle_output_panel(self):
        """切换输出面板的显示状态"""
        if self.output_panel_visible:
            self.output_panel_frame.pack_forget()
            self.output_sash.pack_forget()
            self.output_toggle_btn.config(text="📤 显示输出")
            self.output_panel_visible = False
        else:
            self.output_panel_frame.pack(fill=tk.BOTH, expand=False, pady=(10, 0))
            self.output_sash.pack(fill=tk.X, pady=0)
            self.output_toggle_btn.config(text="📥 隐藏输出")
            self.output_panel_visible = True
    
    def start_resize_output(self, event):
        """开始调整输出面板大小"""
        self.resize_data = {
            "y_start": event.y_root,
            "height_start": self.output_panel_frame.winfo_height()
        }
    
    def resize_output(self, event):
        """调整输出面板大小"""
        if not hasattr(self, 'resize_data'):
            return
        
        delta_y = event.y_root - self.resize_data["y_start"]
        new_height = max(100, min(600, self.resize_data["height_start"] - delta_y))
        
        self.output_panel_frame.config(height=new_height)
        self.output_panel_frame.pack_propagate(False)

    def create_navigation_panel(self):
        """创建左侧导航面板"""
        nav_frame = tk.Frame(self.content_frame, bg="#2c3e50", width=250)
        nav_frame.pack(side=tk.LEFT, fill=tk.Y, padx=(0, 10))
        
        # 导航标题
        nav_title = tk.Label(nav_frame, text="📚 分类导航", bg="#2c3e50", fg="white",
                           font=("Segoe UI", 14, "bold"), pady=15)
        nav_title.pack(fill=tk.X)
        
        # 导航按钮容器
        nav_buttons_frame = tk.Frame(nav_frame, bg="#2c3e50")
        nav_buttons_frame.pack(fill=tk.X, padx=10, pady=5)
        
        # 主页导航按钮
        self.home_nav_btn = tk.Button(nav_buttons_frame, text="🏠 主 页",
                                command=self.show_home,
                                bg="#3498db", fg="white", bd=0, padx=10, pady=8,
                                font=("Segoe UI", 12), width=15)
        self.home_nav_btn.pack(pady=(0, 10))
        
        # 添加分隔线
        tk.Frame(nav_frame, bg="#34495e", height=2).pack(fill=tk.X, pady=10)
        
        # 内置分类标题
        builtin_title = tk.Label(nav_frame, text="📦 内置分类", bg="#2c3e50", fg="#95a5a6",
                               font=("Segoe UI", 11, "bold"), anchor="w", padx=15)
        builtin_title.pack(fill=tk.X, pady=(10, 5))
        
        # 内置分类按钮
        self.builtin_buttons_frame = tk.Frame(nav_frame, bg="#2c3e50")
        self.builtin_buttons_frame.pack(fill=tk.X, padx=10)
        
        # 添加内置分类按钮
        self.builtin_buttons = {}
        for category in self.categories.keys():
            btn = tk.Button(self.builtin_buttons_frame, text=f"📄 {category}",
                           command=lambda c=category: self.switch_category(c),
                           bg="#34495e", fg="white", bd=0, padx=10, pady=6,
                           font=("Segoe UI", 11), anchor="w", width=20)
            btn.pack(fill=tk.X, pady=2)
            self.builtin_buttons[category] = btn
        
        # 添加分隔线
        tk.Frame(nav_frame, bg="#34495e", height=2).pack(fill=tk.X, pady=10)
        
        # 笔记分类标题 (新增)
        notes_title = tk.Label(nav_frame, text="📝 我的笔记", bg="#2c3e50", fg="#95a5a6",
                             font=("Segoe UI", 11, "bold"), anchor="w", padx=15)
        notes_title.pack(fill=tk.X, pady=(10, 5))
        
        # 笔记按钮容器 (新增)
        self.notes_buttons_frame = tk.Frame(nav_frame, bg="#2c3e50")
        self.notes_buttons_frame.pack(fill=tk.X, padx=10)
        
        # 添加笔记按钮 (新增)
        note_btn = tk.Button(self.notes_buttons_frame, text="➕ 新建笔记", 
                           command=self.take_note,
                           bg="#8e44ad", fg="white", bd=0, padx=10, pady=6,
                           font=("Segoe UI", 11), anchor="w", width=20)
        note_btn.pack(fill=tk.X, pady=2)
        
        manage_btn = tk.Button(self.notes_buttons_frame, text="🗂 管理笔记", 
                           command=self.manage_notes,
                           bg="#8e44ad", fg="white", bd=0, padx=10, pady=6,
                           font=("Segoe UI", 11), anchor="w", width=20)
        manage_btn.pack(fill=tk.X, pady=2)
        
        # 添加分隔线
        tk.Frame(nav_frame, bg="#34495e", height=2).pack(fill=tk.X, pady=10)
        
        # 导入文件标题
        imported_title = tk.Label(nav_frame, text="📂📂 导入的文件", bg="#2c3e50", fg="#95a5a6", 
                                font=("Segoe UI", 11, "bold"), anchor="w", padx=15)
        imported_title.pack(fill=tk.X, pady=(10, 5))
        
        # 导入文件容器
        self.imported_files_frame = tk.Frame(nav_frame, bg="#2c3e50")
        self.imported_files_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        
        # 滚动条
        scrollbar = tk.Scrollbar(self.imported_files_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 导入文件列表
        self.imported_listbox = tk.Listbox(
            self.imported_files_frame, 
            bg="#34495e", fg="white", 
            selectbackground="#3498db", 
            highlightthickness=0, 
            borderwidth=0,
            font=("Segoe UI", 11),
            yscrollcommand=scrollbar.set
        )
        self.imported_listbox.pack(fill=tk.BOTH, expand=True)
        
        # 绑定选择事件
        self.imported_listbox.bind('<<ListboxSelect>>', self.on_file_selected)
        
        scrollbar.config(command=self.imported_listbox.yview)
        
        # 添加分隔线
        tk.Frame(nav_frame, bg="#34495e", height=2).pack(fill=tk.X, pady=10)
        
        # 工具按钮
        tools_frame = tk.Frame(nav_frame, bg="#2c3e50")
        tools_frame.pack(fill=tk.X, padx=10, pady=(0, 10))
        
        # 刷新按钮
        refresh_btn = tk.Button(tools_frame, text="🔄🔄 刷新列表", command=self.refresh_file_list,
                              bg="#9b59b6", fg="white", bd=0, padx=10, pady=6,
                              font=("Segoe UI", 11))
        refresh_btn.pack(fill=tk.X, pady=2)
    
    def refresh_file_list(self):
        """刷新文件列表"""
        self.scan_and_import_files()
        self.status_var.set("文件列表已刷新")
    
    def on_file_selected(self, event):
        """处理文件选择事件 - 优化路径获取"""
        selection = self.imported_listbox.curselection()
        if selection:
            index = selection[0]
            file_name = self.imported_listbox.get(index)
            file_path = self.imported_files.get(file_name)
            
            if not file_path or not os.path.exists(file_path):
                messagebox.showerror("错误", f"文件不存在: {file_name}")
                # 从列表中移除无效文件
                self.imported_listbox.delete(index)
                if file_name in self.imported_files:
                    del self.imported_files[file_name]
                return
                
            base_name = os.path.splitext(file_name)[0]
            self.switch_category(base_name, file_path)
    
    def create_menu(self):
        """创建菜单栏"""
        self.menu_bar = Menu(self.root)
        self.root.config(menu=self.menu_bar)
        
        # 文件菜单
        file_menu = Menu(self.menu_bar, tearoff=0)
        file_menu.add_command(label="📄📄 新建文件", command=self.new_file)
        file_menu.add_command(label="📂📂 打开文件", command=self.import_file)
        file_menu.add_command(label="💾💾 保存文件", command=self.save_file)
        file_menu.add_separator()
        file_menu.add_command(label="🚪🚪 退出", command=self.on_closing)
        self.menu_bar.add_cascade(label="文件", menu=file_menu)
        
        # 编辑菜单
        edit_menu = Menu(self.menu_bar, tearoff=0)
        edit_menu.add_command(label="✏✏️ 编辑内容", command=self.modify_content)
        edit_menu.add_command(label="🔍🔍 查找", command=self.focus_search)
        edit_menu.add_separator()
        edit_menu.add_command(label="🔄🔄 格式化代码", command=self.format_code)
        self.menu_bar.add_cascade(label="编辑", menu=edit_menu)
        
        # 工具菜单
        tools_menu = Menu(self.menu_bar, tearoff=0)
        tools_menu.add_command(label="🧮🧮 计算器", command=self.open_calculator)
        tools_menu.add_command(label="🏠🏠 返回主页", command=self.show_home)
        tools_menu.add_command(label="🔄🔄 刷新文件列表", command=self.refresh_file_list)
        tools_menu.add_command(label="📝📝 新建笔记", command=self.take_note)  # 新增
        tools_menu.add_command(label="▶️▶️ 运行代码", command=self.run_python_code)  # 新增
        self.menu_bar.add_cascade(label="工具", menu=tools_menu)
        
        # PDF菜单
        self.pdf_menu = Menu(self.menu_bar, tearoff=0)
        self.pdf_menu.add_command(label="上一页", command=self.prev_pdf_page)
        self.pdf_menu.add_command(label="下一页", command=self.next_pdf_page)
        self.pdf_menu.add_command(label="放大", command=self.zoom_in)
        self.pdf_menu.add_command(label="缩小", command=self.zoom_out)
        self.pdf_menu.add_separator()
        self.pdf_menu.add_command(label="📝📝 提取文本", command=self.extract_pdf_text)
        self.menu_bar.add_cascade(label="PDF", menu=self.pdf_menu)
        # 初始禁用PDF菜单
        self.pdf_menu.entryconfig(0, state="disabled")
        self.pdf_menu.entryconfig(1, state="disabled")
        self.pdf_menu.entryconfig(2, state="disabled")
        self.pdf_menu.entryconfig(3, state="disabled")
        self.pdf_menu.entryconfig(5, state="disabled")
        
        # 收藏菜单
        snippets_menu = Menu(self.menu_bar, tearoff=0)
        snippets_menu.add_command(label="📌📌 添加当前代码片段", command=self.add_snippet)
        snippets_menu.add_command(label="🗂🗂 管理代码片段", command=self.manage_snippets)
        self.menu_bar.add_cascade(label="收藏", menu=snippets_menu)
        
        # 笔记菜单 (新增)
        notes_menu = Menu(self.menu_bar, tearoff=0)
        notes_menu.add_command(label="📝📝 新建笔记", command=self.take_note)
        notes_menu.add_command(label="🗂🗂 管理笔记", command=self.manage_notes)
        self.menu_bar.add_cascade(label="笔记", menu=notes_menu)
        
        # 设置菜单
        settings_menu = Menu(self.menu_bar, tearoff=0)
        self.auto_save_var = tk.BooleanVar(value=True)
        settings_menu.add_checkbutton(label="🔄🔄 自动保存", variable=self.auto_save_var, 
                                    command=self.toggle_auto_save)
        self.menu_bar.add_cascade(label="设置", menu=settings_menu)
    
    def create_home_page(self):
        """创建欢迎主页"""
        self.home_frame = tk.Frame(self.viewer_container, bg="#ffffff", 
                                 highlightthickness=1, highlightbackground="#e0e0e0",
                                 highlightcolor="#64B5F6")
        self.home_frame.pack(fill=tk.BOTH, expand=True)
        
        # 欢迎标题
        welcome_label = tk.Label(self.home_frame, text="欢迎使用分类查看器",
                               bg="white", fg="#2c3e50", 
                               font=("Segoe UI", 24, "bold"))
        welcome_label.pack(pady=(40, 20))
        
        # 应用描述
        desc_text = (
            "这是一个功能贼多的文本查看和管理工具，支持一大堆功能：（后续还会加）\n\n"
            "• 目前实现的功能有：\n"
            "• 分类查看和编辑文本内容\n"
            "• 自动导入目录中的文件\n"
            "• 查看PDF文件（只读）\n"
            "• 内置计算器工具\n"
            "• 文本搜索和替换功能\n"
            "• 固定行号显示\n"
            "• 美观的用户界面\n"
            "• 语法高亮和格式化\n"
            "• PDF文本提取\n"
            "• 代码片段收藏\n"
            "• 笔记功能\n"
            "• 运行Python代码功能\n"
            "• 独立输出面板\n"
            "• 自动保存功能\n\n"
            "使用左侧导航栏或工具栏按钮开始研究吧！"
        )
        desc_label = tk.Label(self.home_frame, text=desc_text, 
                             bg="white", fg="#34495e", justify=tk.LEFT,
                             font=("Segoe UI", 14))
        desc_label.pack(pady=10, padx=40)
        
        # 功能卡片
        card_frame = tk.Frame(self.home_frame, bg="white")
        card_frame.pack(pady=30, padx=40, fill=tk.X)
        
        cards = [
            {"title": "📚 分类管理", "desc": "按类别组织和管理文本内容", "color": "#3498db"},
            {"title": "📂 自动导入", "desc": "自动扫描并导入目录中的文件", "color": "#2ecc71"},
            {"title": "✏✏ 文本编辑", "desc": "拥有编辑和搜索功能", "color": "#9b59b6"},
            {"title": "📄 PDF查看", "desc": "支持PDF文件查看功能", "color": "#e74c3c"},
            {"title": "📝 笔记功能", "desc": "创建和管理个人笔记", "color": "#8e44ad"},
            {"title": "▶️▶ 代码运行", "desc": "可执行Python代码", "color": "#27ae60"},
            {"title": "📤 输出面板", "desc": "独立全局输出显示区域", "color": "#16a085"},
            {"title": "🧰 内置工具", "desc": "包含计算器等实用工具", "color": "#e67e22"}
        ]
        
        for i, card in enumerate(cards):
            card_bg = tk.Frame(card_frame, bg=card["color"], bd=0, 
                              highlightthickness=0, width=200, height=120)
            card_bg.grid(row=0, column=i, padx=10, sticky="nsew")
            card_bg.grid_propagate(False)
            
            card_content = tk.Frame(card_bg, bg="white", padx=10, pady=10)
            card_content.place(relx=0.05, rely=0.05, relwidth=0.9, relheight=0.9)
            
            title_label = tk.Label(card_content, text=card["title"], 
                                 bg="white", fg=card["color"], 
                                 font=("Segoe UI", 14, "bold"))
            title_label.pack(anchor="w", pady=(5, 2))
            
            desc_label = tk.Label(card_content, text=card["desc"], 
                                bg="white", fg="#7f8c8d", 
                                font=("Segoe UI", 11), justify=tk.LEFT)
            desc_label.pack(anchor="w", pady=2)
            
            # 添加悬停效果（修正闭包问题）
            card_bg.bind("<Enter>", lambda e, cb=card_bg, c=card["color"]: cb.configure(bg=self.lighter_color(c)))
            card_bg.bind("<Leave>", lambda e, cb=card_bg, c=card["color"]: cb.configure(bg=c))
        
        # 设置列权重
        for i in range(len(cards)):
            card_frame.columnconfigure(i, weight=1)
        
        # 最近文件标题
        recent_label = tk.Label(self.home_frame, text="⏱⏱⏱️ 最近文件", 
                              bg="white", fg="#2c3e50", 
                              font=("Segoe UI", 16, "bold"))
        recent_label.pack(pady=(40, 10), anchor="w", padx=40)
        
        # 最近文件列表（示例）
        self.recent_files_frame = tk.Frame(self.home_frame, bg="white")
        self.recent_files_frame.pack(fill=tk.X, padx=40, pady=(0, 30))
        
        # 状态栏
        self.status_var = tk.StringVar()
        self.status_var.set("就绪 | 欢迎使用分类查看器")
        status_bar = tk.Label(self.root, textvariable=self.status_var, bd=0, relief=tk.FLAT, 
                             anchor=tk.W, bg="#ecf0f1", fg="#666", font=("Segoe UI", 10))
        status_bar.pack(side=tk.BOTTOM, fill=tk.X, padx=20, pady=(0, 10))
        
        # 添加字数统计到状态栏
        word_count_label = tk.Label(status_bar, textvariable=self.word_count_var, 
                                   font=("Segoe UI", 10))
        word_count_label.pack(side=tk.RIGHT, padx=20)

        # 初始化字数统计
        self.word_count_var.set("字数: 0")
    
    def lighter_color(self, color, factor=0.2):
        """生成更亮的颜色"""
        # 将十六进制颜色转换为RGB
        r = int(color[1:3], 16)
        g = int(color[3:5], 16)
        b = int(color[5:7], 16)
        
        # 增加亮度
        r = min(255, int(r + (255 - r) * factor))
        g = min(255, int(g + (255 - g) * factor))
        b = min(255, int(b + (255 - b) * factor))
        
        # 转换回十六进制
        return f"#{r:02x}{g:02x}{b:02x}"

    def create_text_viewer(self):
        """创建文本查看器"""
        self.text_frame = tk.Frame(self.viewer_container, bg="#ffffff",
                                 highlightthickness=1, highlightbackground="#e0e0e0",
                                 highlightcolor="#64B5F6")
        # 初始隐藏
        self.text_frame.pack_forget()

        # 使用PanedWindow实现可调整大小的分割窗口
        self.text_paned = tk.PanedWindow(self.text_frame, orient=tk.VERTICAL, bg="#f0f2f5", sashwidth=6, sashrelief=tk.RAISED)
        self.text_paned.pack(fill=tk.BOTH, expand=True)

        # 创建代码编辑区域
        code_frame = tk.Frame(self.text_paned, bg="white")
        self.text_paned.add(code_frame)
        
        # 固定行号区域
        self.line_number_frame = tk.Frame(code_frame, bg="#f5f5f5", width=50)
        self.line_number_frame.pack(side=tk.LEFT, fill=tk.Y)

        # 创建行号画布
        self.line_number_canvas = tk.Canvas(self.line_number_frame, bg="#f5f5f5", highlightthickness=0)
        self.line_number_canvas.pack(fill=tk.BOTH, expand=True)

        # 文本查看区域（只读）
        self.text_viewer = scrolledtext.ScrolledText(
            code_frame, wrap=tk.WORD,
            padx=15, pady=10, highlightthickness=0, border=0,
            state="disabled"  # 设置为只读
        )
        self.text_viewer.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        # 设置分割比例（100%给代码）
        self.text_paned.paneconfigure(code_frame, minsize=100)
        
        # 当前分类
        self.current_category = "Python"

        # 添加语法高亮标签
        self.text_viewer.tag_configure("keyword", foreground="#CC3300")
        self.text_viewer.tag_configure("comment", foreground="#339933")
        self.text_viewer.tag_configure("string", foreground="#0066CC")
        self.text_viewer.tag_configure("function", foreground="#990099")
        self.text_viewer.tag_configure("number", foreground="#FF6600")

        # 绑定文本变化事件
        self.text_viewer.bind("<<Modified>>", self.on_text_modified)
    
    def on_text_modified(self, event):
        """处理文本变化事件"""
        if self.text_viewer.edit_modified():
            # 重置修改标记
            self.text_viewer.edit_modified(False)

            # 更新行号显示
            self.update_fixed_line_numbers()

            # 更新字数统计
            self.update_word_count()

    def update_fixed_line_numbers(self, event=None):
        """更新固定行号显示 - 优化版本"""
        if not hasattr(self, 'text_viewer') or not self.text_viewer.winfo_ismapped():
            return

        # 获取总行数
        last_line = self.text_viewer.index("end-1c")
        if not last_line:
            return
            
        total_lines = int(last_line.split('.')[0]) if last_line else 1

        # 计算最大行号位数
        max_digits = max(len(str(total_lines)), 1)  # 至少1位

        # 使用字体实际宽度计算
        char_width = self.viewer_font.measure("0")
        new_width = char_width * max_digits + 20  # 增加边距

        # 更新行号区域宽度
        if self.line_number_frame.cget("width") != new_width:
            self.line_number_frame.config(width=new_width)
            self.line_number_frame.update_idletasks()

        # 清除画布内容
        self.line_number_canvas.delete("all")

        # 获取当前可见行范围
        first_visible_line = int(self.text_viewer.index("@0,0").split('.')[0])
        last_visible_line = int(self.text_viewer.index(f"@0,{self.text_viewer.winfo_height()}").split('.')[0])

        # 确保不超过总行数
        last_visible_line = min(last_visible_line, total_lines)

        # 绘制行号
        y_offset = 5
        line_height = self.viewer_font.metrics("linespace")
        canvas_width = self.line_number_frame.winfo_width()
        canvas_height = self.line_number_canvas.winfo_height()

        for line_num in range(first_visible_line, last_visible_line + 1):
            # 绘制行号
            y_pos = y_offset + (line_num - first_visible_line) * line_height
            self.line_number_canvas.create_text(
                canvas_width - 5,  # 右对齐
                y_pos,
                text=str(line_num),
                anchor=tk.E,
                fill="#666",
                font=self.viewer_font
            )

            # 每隔50行添加一条虚线
            if line_num % 50 == 0 and line_num > 0:
                # 创建虚线
                self.line_number_canvas.create_line(
                    0, y_pos + line_height / 2,
                    canvas_width, y_pos + line_height / 2,
                    fill="#888", dash=(2, 2), width=1
                )

                # 在虚线上方添加标记文本
                self.line_number_canvas.create_text(
                    5, y_pos + line_height / 2 - 10,  # 文本位置在虚线上方
                    text=f"此处为第{line_num}行",
                    anchor=tk.W,
                    fill="#666",
                    font=("Segoe UI", 9)
                )
    
    def create_pdf_viewer(self):
        """创建PDF查看器"""
        self.pdf_frame = tk.Frame(self.viewer_container, bg="#ffffff", 
                                highlightthickness=1, highlightbackground="#e0e0e0")
        # 初始隐藏
        self.pdf_frame.pack_forget()
        
        # 创建PDF显示区域
        pdf_container = tk.Frame(self.pdf_frame, bg="#f0f2f5")
        pdf_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 滚动条
        self.pdf_scrollbar = tk.Scrollbar(pdf_container)
        self.pdf_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 创建Canvas用于显示PDF页面
        self.pdf_canvas = tk.Canvas(
            pdf_container, 
            bg="white", 
            yscrollcommand=self.pdf_scrollbar.set
        )
        self.pdf_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        self.pdf_scrollbar.config(command=self.pdf_canvas.yview)
        
        # 绑定鼠标滚轮事件
        self.pdf_canvas.bind("<MouseWheel>", self.on_pdf_scroll)
        self.pdf_canvas.bind("<Configure>", self.resize_pdf)
    
    def on_pdf_scroll(self, event):
        """处理PDF滚动事件"""
        if event.delta < 0:
            self.pdf_canvas.yview_scroll(1, "units")
        else:
            self.pdf_canvas.yview_scroll(-1, "units")
    
    def resize_pdf(self, event=None):
        """调整PDF大小"""
        if self.current_pdf:
            self.show_pdf_page()
    
    def set_dpi_aware(self):
        """设置DPI感知以提高高分辨率显示效果"""
        if sys.platform == "win32":
            try:
                from ctypes import windll
                windll.shcore.SetProcessDpiAwareness(1)
            except:
                pass
        self.root.tk.call('tk', 'scaling', 1.5)  # 增加缩放因子
    
    def set_font(self):
        """设置高分辨率友好字体"""
        # 文本查看器字体
        self.viewer_font = font.Font(family="Consolas", size=14)
        if hasattr(self, 'text_viewer'):
            self.text_viewer.configure(font=self.viewer_font)
        
        # 输出文本字体
        if hasattr(self, 'output_text'):
            self.output_text.configure(font=("Consolas", 12))
        
        # 主页字体
        if hasattr(self, 'home_frame'):
            for widget in self.home_frame.winfo_children():
                if isinstance(widget, tk.Label):
                    widget.configure(font=("Segoe UI", 12))
    
    def show_home(self):
        """显示主页"""
        if hasattr(self, 'text_frame') and self.text_frame.winfo_ismapped():
            self.text_frame.pack_forget()
        if hasattr(self, 'pdf_frame') and self.pdf_frame.winfo_ismapped():
            self.pdf_frame.pack_forget()
            # 隐藏PDF导航按钮
            self.pdf_nav_frame.pack_forget()
            # 禁用PDF菜单
            self.pdf_menu.entryconfig(0, state="disabled")
            self.pdf_menu.entryconfig(1, state="disabled")
            self.pdf_menu.entryconfig(2, state="disabled")
            self.pdf_menu.entryconfig(3, state="disabled")
            self.pdf_menu.entryconfig(5, state="disabled")
        if hasattr(self, 'home_frame'):
            self.home_frame.pack(fill=tk.BOTH, expand=True)
        self.status_var.set("就绪 | 欢迎使查看器")
        self.title_label.configure(text="分类查看器")
    
    def show_text_viewer(self):
        """显示文本查看器"""
        if hasattr(self, 'home_frame') and self.home_frame.winfo_ismapped():
            self.home_frame.pack_forget()
        if hasattr(self, 'pdf_frame') and self.pdf_frame.winfo_ismapped():
            self.pdf_frame.pack_forget()
            # 隐藏PDF导航按钮
            self.pdf_nav_frame.pack_forget()
            # 禁用PDF菜单
            self.pdf_menu.entryconfig(0, state="disabled")
            self.pdf_menu.entryconfig(1, state="disabled")
            self.pdf_menu.entryconfig(2, state="disabled")
            self.pdf_menu.entryconfig(3, state="disabled")
            self.pdf_menu.entryconfig(5, state="disabled")
        if hasattr(self, 'text_frame'):
            self.text_frame.pack(fill=tk.BOTH, expand=True)
    
    def show_pdf_viewer(self):
        """显示PDF查看器"""
        if hasattr(self, 'home_frame') and self.home_frame.winfo_ismapped():
            self.home_frame.pack_forget()
        if hasattr(self, 'text_frame') and self.text_frame.winfo_ismapped():
            self.text_frame.pack_forget()
        if hasattr(self, 'pdf_frame'):
            self.pdf_frame.pack(fill=tk.BOTH, expand=True)
            # 显示PDF导航按钮
            self.pdf_nav_frame.pack(side=tk.RIGHT, padx=10)
            # 启用PDF菜单
            self.pdf_menu.entryconfig(0, state="normal")
            self.pdf_menu.entryconfig(1, state="normal")
            self.pdf_menu.entryconfig(2, state="normal")
            self.pdf_menu.entryconfig(3, state="normal")
            self.pdf_menu.entryconfig(5, state="normal")
    
    def switch_category(self, category, file_path=None):
        """切换到指定分类"""
        # 重置PDF状态
        if self.current_pdf:
            self.current_pdf.close()
            self.current_pdf = None
            self.current_pdf_page = 0
            self.pdf_images = []
        
        # 重置笔记状态
        self.current_note_id = None
        
        # 如果是PDF文件
        if file_path and file_path.lower().endswith('.pdf'):
            try:
                self.current_pdf = fitz.open(file_path)
                self.current_pdf_page = 0
                self.current_file_path = file_path
                self.content_modified_flag = False
                
                # 显示PDF查看器
                self.show_pdf_viewer()
                self.show_pdf_page()
                
                # 更新标题
                self.title_label.configure(text=f"PDF查看器 - {os.path.basename(file_path)}")
                self.status_var.set(f"已加载PDF: {os.path.basename(file_path)} | 当前分类: {category}")
                
                # 创建PDF导航按钮
                self.create_pdf_navigation()
                
                return
            except Exception as e:
                messagebox.showerror("错误", f"加载PDF失败:\n{str(e)}")
                self.status_var.set(f"加载失败 | 当前分类: {category}")
                return
        
        # 文本文件处理
        self.show_text_viewer()
        self.current_category = category
        
        # 更新标题
        self.title_label.configure(text=f"分类查看器 - {category}")
        
        # 加载分类内容
        self.text_viewer.config(state="normal")  # 临时启用以更新内容
        self.text_viewer.delete(1.0, tk.END)
        
        if file_path:
            # 从文件加载内容
            try:
                with open(file_path, "r", encoding="utf-8") as file:
                    content = file.read()
                
                # 应用语法高亮
                self.text_viewer.insert(tk.END, content)
                self.apply_syntax_highlighting()
                
                self.current_file_path = file_path
                self.content_modified_flag = False
                self.status_var.set(f"已加载: {os.path.basename(file_path)} | 只读模式 | 当前分类: {category}")
            except Exception as e:
                messagebox.showerror("错误", f"加载文件失败:\n{str(e)}")
                self.text_viewer.insert(tk.END, self.categories.get(category, "内容加载失败"))
                self.status_var.set(f"加载失败 | 当前分类: {category}")
        else:
            # 加载内置分类内容
            self.text_viewer.insert(tk.END, self.categories.get(category, "内容未找到"))
            self.current_file_path = None
            self.content_modified_flag = False
            self.status_var.set(f"已切换到分类: {category} | 只读模式 | 当前分类: {category}")
        
        # 设置为只读模式
        self.text_viewer.config(state="disabled")
        
        # 更新行号和字数
        self.update_fixed_line_numbers()
        self.update_word_count()
        
        # 清空输出面板
        self.clear_output()
    
    def apply_syntax_highlighting(self):
        """应用语法高亮"""
        # 清除之前的高亮
        for tag in ["keyword", "comment", "string", "function", "number"]:
            self.text_viewer.tag_remove(tag, "1.0", tk.END)
        
        # 获取文本内容
        content = self.text_viewer.get("1.0", tk.END)
        
        # Python关键字列表
        python_keywords = [
            "False", "None", "True", "and", "as", "assert", "async", "await", 
            "break", "class", "continue", "def", "del", "elif", "else", "except", 
            "finally", "for", "from", "global", "if", "import", "in", "is", 
            "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try", 
            "while", "with", "yield"
        ]
        
        # C++关键字列表
        cpp_keywords = [
            "auto", "break", "case", "char", "const", "continue", "default", 
            "do", "double", "else", "enum", "extern", "float", "for", "goto", 
            "if", "int", "long", "register", "return", "short", "signed", 
            "sizeof", "static", "struct", "switch", "typedef", "union", 
            "unsigned", "void", "volatile", "while", "class", "public", 
            "private", "protected", "virtual", "template", "using", "namespace"
        ]
        
        # 根据当前分类决定使用哪种高亮规则
        if "Python" in self.current_category:
            keywords = python_keywords
        elif "C++" in self.current_category:
            keywords = cpp_keywords
        else:
            # 默认使用Python高亮
            keywords = python_keywords
        
        # 高亮关键字
        for keyword in keywords:
            start = "1.0"
            while True:
                start = self.text_viewer.search(r"\m{}\M".format(keyword), start, stopindex=tk.END, regexp=True)
                if not start:
                    break
                end = f"{start}+{len(keyword)}c"
                self.text_viewer.tag_add("keyword", start, end)
                start = end
        
        # 高亮注释
        start = "1.0"
        while True:
            start = self.text_viewer.search(r"#.*", start, stopindex=tk.END, regexp=True)
            if not start:
                break
            end = self.text_viewer.index(f"{start} lineend")
            self.text_viewer.tag_add("comment", start, end)
            start = end
        
        # 高亮字符串
        start = "1.0"
        while True:
            start = self.text_viewer.search(r"[\"'].*?[\"']", start, stopindex=tk.END, regexp=True)
            if not start:
                break
            end = self.text_viewer.index(f"{start} lineend")
            self.text_viewer.tag_add("string", start, end)
            start = end
        
        # 高亮函数名
        start = "1.0"
        while True:
            start = self.text_viewer.search(r"def\s+(\w+)\s*\(", start, stopindex=tk.END, regexp=True)
            if not start:
                break
            # 获取函数名开始位置
            func_start = self.text_viewer.index(f"{start}+4c")
            # 获取函数名结束位置
            end_search = self.text_viewer.search(r"\(", func_start, stopindex=tk.END)
            if not end_search:
                break
            func_end = self.text_viewer.index(f"{end_search}-1c")
            self.text_viewer.tag_add("function", func_start, func_end)
            start = end_search
        
        # 高亮数字
        start = "1.0"
        while True:
            start = self.text_viewer.search(r"\b\d+\b", start, stopindex=tk.END, regexp=True)
            if not start:
                break
            end = self.text_viewer.index(f"{start} wordend")
            self.text_viewer.tag_add("number", start, end)
            start = end
    
    def create_pdf_navigation(self):
        """创建PDF导航控件"""
        # 清除现有控件
        for widget in self.pdf_nav_frame.winfo_children():
            widget.destroy()

        # 上一页按钮
        prev_btn = tk.Button(self.pdf_nav_frame, text="⬅️ 上一页", 
                            command=self.prev_pdf_page,
                            bg="#3498db", fg="white", bd=0, padx=10, pady=6)
        prev_btn.pack(side=tk.LEFT, padx=5)
        
        # 页码显示
        page_label = tk.Label(self.pdf_nav_frame, textvariable=self.pdf_page_var, 
                            bg="#f0f2f5", font=("Segoe UI", 11))
        page_label.pack(side=tk.LEFT, padx=5)
        
        # 下一页按钮
        next_btn = tk.Button(self.pdf_nav_frame, text="➡️ 下一页", 
                            command=self.next_pdf_page,
                            bg="#3498db", fg="white", bd=0, padx=10, pady=6)
        next_btn.pack(side=tk.LEFT, padx=5)
        
        # 放大按钮
        zoom_in_btn = tk.Button(self.pdf_nav_frame, text="➕ 放大", 
                              command=self.zoom_in,
                              bg="#2ecc71", fg="white", bd=0, padx=10, pady=6)
        zoom_in_btn.pack(side=tk.LEFT, padx=5)
        
        # 缩小按钮
        zoom_out_btn = tk.Button(self.pdf_nav_frame, text="➖ 缩小", 
                               command=self.zoom_out,
                               bg="#e74c3c", fg="white", bd=0, padx=10, pady=6)
        zoom_out_btn.pack(side=tk.LEFT, padx=5)
        
        # 更新页码显示
        self.update_pdf_page_display()
    
    def update_pdf_page_display(self):
        """更新PDF页码显示"""
        if self.current_pdf:
            self.pdf_page_var.set(f"页码: {self.current_pdf_page+1}/{len(self.current_pdf)}")
    
    def show_pdf_page(self):
        """显示当前PDF页面"""
        if not self.current_pdf or self.current_pdf_page < 0 or self.current_pdf_page >= len(self.current_pdf):
            return
        
        # 清除之前的图像
        self.pdf_images = []
        
        # 获取页面
        page = self.current_pdf.load_page(self.current_pdf_page)
        
        # 获取Canvas尺寸
        canvas_width = self.pdf_canvas.winfo_width()
        canvas_height = self.pdf_canvas.winfo_height()
        
        # 计算缩放比例（基于Canvas宽度）
        zoom = min(1.0, canvas_width / 595) * self.pdf_scale  # 595是A4纸的宽度(px)
        
        # 创建矩阵用于缩放
        mat = fitz.Matrix(zoom, zoom)
        
        # 获取页面图像
        pix = page.get_pixmap(matrix=mat)
        
        # 转换为PIL图像
        img = Image.frombytes("RGB", [pix.width, pix.height], pix.samples)
        
        # 转换为Tkinter PhotoImage
        self.pdf_image = ImageTk.PhotoImage(img)
        self.pdf_images.append(self.pdf_image)  # 保持引用
        
        # 清除Canvas并显示新图像
        self.pdf_canvas.delete("all")
        self.pdf_canvas.create_image(
            (canvas_width - self.pdf_image.width()) // 2, 
            10, 
            image=self.pdf_image, 
            anchor="nw"
        )
        
        # 设置Canvas滚动区域
        self.pdf_canvas.config(scrollregion=(
            0, 0, 
            max(canvas_width, self.pdf_image.width()), 
            max(canvas_height, self.pdf_image.height() + 20)
        ))
        
        # 更新页码显示
        self.update_pdf_page_display()
    
    def prev_pdf_page(self):
        """显示上一页PDF"""
        if self.current_pdf and self.current_pdf_page > 0:
            self.current_pdf_page -= 1
            self.show_pdf_page()
    
    def next_pdf_page(self):
        """显示下一页PDF"""
        if self.current_pdf and self.current_pdf_page < len(self.current_pdf) - 1:
            self.current_pdf_page += 1
            self.show_pdf_page()
    
    def zoom_in(self):
        """放大PDF"""
        self.pdf_scale = min(2.0, self.pdf_scale + 0.1)
        self.show_pdf_page()
    
    def zoom_out(self):
        """缩小PDF"""
        self.pdf_scale = max(0.5, self.pdf_scale - 0.1)
        self.show_pdf_page()
    
    def create_tags(self):
        """创建文本标签"""
        if hasattr(self, 'text_viewer'):
            # 搜索高亮标签
            self.text_viewer.tag_configure("search_highlight", background="#FFF9C4", foreground="black")
            self.text_viewer.tag_configure("current_search", background="#FFD54F", foreground="black")
    
    def bind_events(self):
        """绑定事件"""
        if hasattr(self, 'text_viewer'):
            # 滚动时更新固定行号
            self.text_viewer.bind("<MouseWheel>", self.update_fixed_line_numbers)
            self.text_viewer.bind("<Button-4>", self.update_fixed_line_numbers)
            self.text_viewer.bind("<Button-5>", self.update_fixed_line_numbers)

            # 搜索框回车事件
            self.search_entry.bind("<Return>", lambda event: self.search_text())
        
        # 关闭窗口前询问保存
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
    
    def new_file(self):
        """新建文件"""
        # 如果是PDF文件，不能新建
        if self.current_pdf:
            messagebox.showinfo("提示", "PDF文件不支持新建操作")
            return
        
        # 检查当前内容是否已修改
        if self.content_modified():
            if messagebox.askyesno("新建文件", "当前内容已修改，是否保存？"):
                if not self.save_file():
                    return  # 如果保存失败，不创建新文件
        
        # 清空当前内容
        self.text_viewer.config(state="normal")
        self.text_viewer.delete(1.0, tk.END)
        self.text_viewer.config(state="disabled")  # 设置为只读
        
        self.update_fixed_line_numbers()
        self.update_word_count()
        self.current_file_path = None
        self.content_modified_flag = False
        self.status_var.set(f"已创建新文件 | 只读模式 | 当前分类: {self.current_category}")
        
        # 清空输出面板
        self.clear_output()
    
    def content_modified(self):
        """检查内容是否已修改"""
        return self.content_modified_flag
    
    def import_file(self):
        """导入文件并替换当前内容"""
        # 检查当前内容是否已修改
        if self.content_modified():
            if messagebox.askyesno("导入文件", "当前内容已修改，是否保存？"):
                self.save_file()
        
        file_path = filedialog.askopenfilename(
            filetypes=[("文本文件", "*.txt *.md *.py"), ("PDF文件", "*.pdf"), ("所有文件", "*.*")]
        )
        if file_path:
            self.add_file_to_list(file_path)
            self.switch_category(os.path.basename(file_path), file_path)
            self.save_imported_files()  # 保存导入的文件列表
    
    def scan_and_import_files(self):
        """扫描当前目录并导入文件，同时加载记忆的文件"""
        # 1. 加载记忆的文件
        self.load_imported_files()
        
        # 2. 扫描当前目录并导入文件
        current_dir = os.path.dirname(os.path.abspath(__file__))
        for file in os.listdir(current_dir):
            if file.lower().endswith((".txt", ".pdf", ".md", ".py")):
                file_path = os.path.join(current_dir, file)
                # 避免重复添加
                if file_path not in self.imported_files.values():
                    self.add_file_to_list(file_path)
        
        # 3. 保存更新后的文件列表
        self.save_imported_files()
    
    def add_file_to_list(self, file_path):
        """添加文件到列表 - 优化显示"""
        file_name = os.path.basename(file_path)
        # 添加到导入文件字典
        self.imported_files[file_name] = file_path
        
        # 添加到列表控件（只显示文件名）
        self.imported_listbox.insert(tk.END, file_name)
    
    def save_imported_files(self):
        """保存导入的文件列表到配置文件"""
        config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "imported_files.json")
        try:
            with open(config_path, "w", encoding="utf-8") as f:
                json.dump(self.imported_files, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"保存导入文件列表失败: {str(e)}")
    
    def load_imported_files(self):
        """从配置文件加载导入的文件列表"""
        config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "imported_files.json")
        
        # 如果配置文件不存在，则创建空字典
        if not os.path.exists(config_path):
            self.imported_files = {}
            return
        
        try:
            with open(config_path, "r", encoding="utf-8") as f:
                self.imported_files = json.load(f)
            
            # 清空列表
            self.imported_listbox.delete(0, tk.END)
            
            # 将导入的文件添加到列表
            for file_name, file_path in self.imported_files.items():
                self.imported_listbox.insert(tk.END, file_name)
        except Exception as e:
            print(f"加载导入文件列表失败: {str(e)}")
            self.imported_files = {}
    
    def save_file(self):
        """保存当前内容到文件"""
        # 如果是PDF文件，不能保存
        if self.current_pdf:
            messagebox.showinfo("提示", "PDF文件不支持保存操作")
            return False
        
        if not self.current_file_path:
            # 如果是新文件，弹出另存为对话框
            file_path = filedialog.asksaveasfilename(
                defaultextension=".txt",
                filetypes=[("文本文件", "*.txt"), ("Python文件", "*.py"), ("Markdown文件", "*.md"), ("所有文件", "*.*")]
            )
            if not file_path:
                return False
            self.current_file_path = file_path
        else:
            file_path = self.current_file_path
        
        try:
            # 临时启用文本编辑器以获取内容
            self.text_viewer.config(state="normal")
            content = self.text_viewer.get(1.0, tk.END)
            self.text_viewer.config(state="disabled")  # 恢复为只读
            
            with open(file_path, "w", encoding="utf-8") as file:
                file.write(content)
            self.content_modified_flag = False
            
            # 如果文件不在导入列表中，则添加
            file_name = os.path.basename(file_path)
            if file_name not in self.imported_files:
                self.imported_files[file_name] = file_path
                self.add_file_to_list(file_path)
                self.save_imported_files()
            
            self.status_var.set(f"文件已保存至: {os.path.basename(file_path)} | 只读模式 | 当前分类: {self.current_category}")
            self.update_word_count()
            return True
        except Exception as e:
            messagebox.showerror("错误", f"保存文件失败:\n{str(e)}")
            return False
    
    def modify_content(self):
        """打开编辑对话框"""
        # 如果是PDF文件，不能编辑
        if self.current_pdf:
            messagebox.showinfo("提示", "PDF文件不支持编辑操作")
            return
            
        if not hasattr(self, 'text_viewer') or not self.text_viewer.winfo_ismapped():
            messagebox.showinfo("提示", "请先选择一个分类或文件")
            return
        
        # 创建编辑对话框
        modify_dialog = tk.Toplevel(self.root)
        modify_dialog.title("编辑内容")
        modify_dialog.geometry("1200x900")
        modify_dialog.transient(self.root)
        modify_dialog.grab_set()
        self.set_dialog_icon(modify_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(modify_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text=f"✏️ 编辑文本内容 - {self.current_category}", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 创建编辑区域
        editor_frame = tk.Frame(dialog_frame, bg="white", highlightthickness=1, 
                               highlightbackground="#E0E0E0", highlightcolor="#64B5F6")
        editor_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 15))
        
        # 文本编辑区域（可编辑）
        text_editor = scrolledtext.ScrolledText(
            editor_frame, wrap=tk.WORD, 
            padx=15, pady=10, highlightthickness=0, border=0,
            font=self.viewer_font  # 使用与主视图相同的字体
        )
        text_editor.pack(fill=tk.BOTH, expand=True)
        
        # 加载当前内容到编辑器（临时启用主查看器以获取内容）
        self.text_viewer.config(state="normal")
        current_content = self.text_viewer.get(1.0, tk.END)
        self.text_viewer.config(state="disabled")
        text_editor.insert(tk.END, current_content)
        
        # 创建按钮区域
        button_frame = tk.Frame(dialog_frame, bg="white")
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        # 保存按钮
        save_btn = tk.Button(button_frame, text="💾 保存", 
                            command=lambda: self.save_changes(modify_dialog, text_editor), 
                            bg="#4CAF50", fg="white", bd=0, padx=20, pady=8)
        save_btn.pack(side=tk.LEFT, padx=5)
        
        # 取消按钮
        cancel_btn = tk.Button(button_frame, text="❌ 取消", command=modify_dialog.destroy, 
                              bg="#F44336", fg="white", bd=0, padx=20, pady=8)
        cancel_btn.pack(side=tk.RIGHT, padx=5)
    
    def save_changes(self, dialog, editor):
        """保存修改后的内容 - 简化逻辑"""
        try:
            # 获取编辑后的内容
            new_content = editor.get(1.0, tk.END)
            
            # 更新主查看器内容（临时启用编辑）
            self.text_viewer.config(state="normal")
            self.text_viewer.delete(1.0, tk.END)
            self.text_viewer.insert(tk.END, new_content)
            
            # 应用语法高亮
            self.apply_syntax_highlighting()
            
            self.text_viewer.config(state="disabled")  # 重新设置为只读
            
            # 标记内容已修改
            self.content_modified_flag = True
            
            # 同时更新分类内容
            if self.current_category in self.categories:
                self.categories[self.current_category] = new_content
            
            # 关闭对话框
            dialog.destroy()
            
            # 更新状态和字数
            if self.current_file_path:
                filename = os.path.basename(self.current_file_path)
                self.status_var.set(f"内容已更新: {filename} | 只读模式")
            else:
                self.status_var.set(f"内容已更新 | 只读模式 | 当前分类: {self.current_category}")
            
            self.update_word_count()
        except Exception as e:
            messagebox.showerror("错误", f"保存修改失败:\n{str(e)}")
    
    def search_text(self):
        """搜索文本"""
        # 如果是PDF文件，不能搜索
        if self.current_pdf:
            messagebox.showinfo("提示", "PDF文件不支持文本搜索")
            return
            
        if not hasattr(self, 'text_viewer') or not self.text_viewer.winfo_ismapped():
            messagebox.showinfo("提示", "请先选择一个分类或文件")
            return
        
        self.search_term = self.search_entry.get().strip()
        if not self.search_term:
            messagebox.showinfo("提示", "请输入搜索内容")
            return
        
        # 清除之前的高亮
        self.text_viewer.tag_remove("search_highlight", "1.0", tk.END)
        self.text_viewer.tag_remove("current_search", "1.0", tk.END)
        
        # 获取文本内容（临时启用编辑以搜索）
        self.text_viewer.config(state="normal")
        content = self.text_viewer.get(1.0, tk.END)
        self.text_viewer.config(state="disabled")
        
        self.search_results = []
        
        # 执行搜索
        pattern = re.compile(re.escape(self.search_term), re.IGNORECASE)
        for match in pattern.finditer(content):
            start_index = f"1.0 + {match.start()} chars"
            end_index = f"1.0 + {match.end()} chars"
            self.search_results.append((start_index, end_index))
            
            # 添加高亮标签（临时启用编辑）
            self.text_viewer.config(state="normal")
            self.text_viewer.tag_add("search_highlight", start_index, end_index)
            self.text_viewer.config(state="disabled")
        
        if not self.search_results:
            messagebox.showinfo("搜索结果", "未找到匹配项")
            self.status_var.set(f"未找到匹配项 | 当前分类: {self.current_category}")
            self.current_search_index = -1
            return
        
        # 设置第一个结果为当前选中项
        self.current_search_index = 0
        self.highlight_current_search()
        self.status_var.set(f"找到 {len(self.search_results)} 个匹配项 | 当前分类: {self.current_category}")
    
    def highlight_current_search(self):
        """高亮当前搜索结果"""
        if not self.search_results or self.current_search_index < 0:
            return
        
        # 清除之前的当前高亮（临时启用编辑）
        self.text_viewer.config(state="normal")
        self.text_viewer.tag_remove("current_search", "1.0", tk.END)
        
        # 获取当前结果位置
        start_index, end_index = self.search_results[self.current_search_index]
        
        # 添加当前高亮标签
        self.text_viewer.tag_add("current_search", start_index, end_index)
        self.text_viewer.config(state="disabled")
        
        # 滚动到当前结果
        self.text_viewer.see(start_index)
        
        # 更新状态
        self.status_var.set(f"第 {self.current_search_index + 1} / {len(self.search_results)} 个匹配项 | 当前分类: {self.current_category}")
    
    def next_result(self):
        """下一个搜索结果"""
        if not self.search_results:
            return
        
        self.current_search_index = (self.current_search_index + 1) % len(self.search_results)
        self.highlight_current_search()
    
    def open_calculator(self):
        """打开计算器对话框"""
        calc_dialog = tk.Toplevel(self.root)
        calc_dialog.title("内置计算器")
        calc_dialog.geometry("400x500")
        calc_dialog.transient(self.root)
        calc_dialog.grab_set()
        self.set_dialog_icon(calc_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(calc_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text="🧮 内置计算器", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 输入框
        self.calc_var = tk.StringVar()
        calc_entry = tk.Entry(dialog_frame, textvariable=self.calc_var, 
                             font=("Consolas", 14), justify=tk.RIGHT,
                             highlightthickness=1, highlightcolor="#64B5F6")
        calc_entry.pack(fill=tk.X, pady=(0, 15))
        calc_entry.focus()
        
        # 结果标签
        self.calc_result = tk.StringVar()
        result_label = tk.Label(dialog_frame, textvariable=self.calc_result, 
                              bg="white", fg="#333", font=("Consolas", 14), 
                              anchor=tk.E, justify=tk.RIGHT)
        result_label.pack(fill=tk.X, pady=(0, 15))
        
        # 按钮网格
        buttons_frame = tk.Frame(dialog_frame, bg="white")
        buttons_frame.pack(fill=tk.BOTH, expand=True)
        
        # 按钮布局
        button_rows = [
            ['C', '⌫', '%', '/'],
            ['7', '8', '9', '*'],
            ['4', '5', '6', '-'],
            ['1', '2', '3', '+'],
            ['0', '.', '=']
        ]
        
        # 配置按钮网格的行和列
        for i in range(5):
            buttons_frame.rowconfigure(i, weight=1)
        for j in range(4):
            buttons_frame.columnconfigure(j, weight=1)
        
        for r, row in enumerate(button_rows):
            for c, btn in enumerate(row):
                # 设置按钮样式
                if btn in ['C', '⌫', '%', '/', '*', '-', '+']:
                    bg_color = "#616161"  # 灰色操作符
                elif btn == '=':
                    bg_color = "#FF9800"  # 橙色等号
                else:
                    bg_color = "#E0E0E0"  # 灰色数字
                
                # 对于'0'按钮，让它跨两列
                if btn == '0' and r == 4:
                    tk.Button(buttons_frame, text=btn, font=("Segoe UI", 12),
                              command=lambda b=btn: self.on_calculator_button(b),
                              bg=bg_color, fg="black" if bg_color == "#E0E0E0" else "white",
                              bd=0, relief="ridge").grid(
                              row=r, column=c, columnspan=2, sticky="nsew", padx=2, pady=2)
                # 对于'='按钮，让它跨两列
                elif btn == '=' and r == 4:
                    tk.Button(buttons_frame, text=btn, font=("Segoe UI", 12),
                              command=lambda b=btn: self.on_calculator_button(b),
                              bg=bg_color, fg="black" if bg_color == "#E0E0E0" else "white",
                              bd=0, relief="ridge").grid(
                              row=r, column=2, columnspan=2, sticky="nsew", padx=2, pady=2)
                else:
                    tk.Button(buttons_frame, text=btn, font=("Segoe UI", 12),
                              command=lambda b=btn: self.on_calculator_button(b),
                              bg=bg_color, fg="black" if bg_color == "#E0E0E0" else "white",
                              bd=0, relief="ridge").grid(
                              row=r, column=c, sticky="nsew", padx=2, pady=2)
    
    def on_calculator_button(self, value):
        """处理计算器按钮点击"""
        current = self.calc_var.get()
        
        # 清除计算结果
        self.calc_result.set("")
        
        if value == '=':
            self.calculate()
        elif value == 'C':
            self.calc_var.set("")
        elif value == '⌫':  # 退格键
            if current:
                self.calc_var.set(current[:-1])
        elif value == '%':
            try:
                # 百分比计算
                if current:
                    result = eval(current) / 100
                    self.calc_var.set(str(result))
            except:
                self.calc_result.set("错误")
        else:
            # 避免连续多个运算符
            if current and current[-1] in ['+', '-', '*', '/'] and value in ['+', '-', '*', '/']:
                self.calc_var.set(current[:-1] + value)
            else:
                self.calc_var.set(current + value)
    
    def calculate(self):
        """执行计算"""
        try:
            expression = self.calc_var.get()
            if not expression:
                return
                
            # 替换可能的数学符号
            expression = expression.replace('×', '*').replace('÷', '/')
            
            # 安全评估表达式
            result = eval(expression)
            self.calc_result.set(f"= {result}")
        except Exception as e:
            self.calc_result.set(f"错误: {str(e)}")
    
    def update_time(self):
        """更新时间显示"""
        now = datetime.datetime.now()
        self.time_var.set(now.strftime("%Y-%m-%d %H:%M:%S"))
        self.root.after(1000, self.update_time)  # 每秒更新一次
    
    def set_dialog_icon(self, dialog):
        """设置对话框图标"""
        try:
            # 使用base64编码的简单图标
            icon_data = """
            R0lGODlhEAAQAMQAAOjo6KWlpaampqenp6qqqqurq6ysrK2tra6urq+vr7CwsLGxsbKysrOzs7S0
            tLW1tba2tre3t7i4uLm5ubq6uru7u7y8vL29vb6+vr+/v8DAwMHBwcLCwsPDw8TExMXFxcbGxsfH
            x8jIyMnJycrKysvLy8zMzM3Nzc7Ozs/Pz9DQ0NHR0dLS0tPT09TU1NXV1dbW1tfX19jY2NnZ2dra
            2tvb29zc3N3d3d7e3t/f3+Dg4OHh4eLi4uPj4+Tk5OXl5ebm5ufn5+jo6Onp6erq6uvr6+zs7O3t
            7e7u7u/v7/Dw8PHx8fLy8vPz8/T09PX19fb29vf39/j4+Pn5+fr6+vv7+/z8/P39/f7+/v///yH5
            BAAAAAAALAAAAAAQABAAAAVqICCOZGmeaKqubOu+cCzPdG3feK7vfO//wKBwSCwaj8ikcslsOp/Q
            qHRKrVqv2Kx2y+16v+CweEwum8/otHrNbrvf8Lh8Tq/b7/i8fs/v+/+AgYKDhIWGh4iJiouMjY6P
            kJGSk5SVlhcAOw==
            """
            icon_bytes = base64.b64decode(icon_data)
            icon_photo = tk.PhotoImage(data=icon_bytes)
            dialog.iconphoto(False, icon_photo)
        except:
            pass
    
    def on_closing(self):
        """关闭窗口时的处理"""
        # 检查内容是否已修改
        if hasattr(self, 'content_modified_flag') and self.content_modified_flag:
            if messagebox.askyesno("退出", "当前内容已修改，是否保存？"):
                if not self.save_file():
                    return  # 如果保存失败，不关闭窗口
        
        # 保存导入的文件列表
        self.save_imported_files()
        
        # 保存代码片段
        self.save_snippets()
        
        # 保存笔记
        self.save_notes()
        
        # 关闭打开的PDF文件
        if self.current_pdf:
            self.current_pdf.close()
        
        # 停止自动保存线程
        self.stop_auto_save()
        
        self.root.destroy()
    
    def focus_search(self):
        """聚焦到搜索框"""
        self.search_entry.focus_set()
        self.search_entry.select_range(0, tk.END)
    
    def extract_pdf_text(self):
        """提取PDF文本内容"""
        if not self.current_pdf:
            messagebox.showinfo("提示", "请先打开一个PDF文件")
            return
        
        # 创建文本提取对话框
        extract_dialog = tk.Toplevel(self.root)
        extract_dialog.title("PDF文本提取")
        extract_dialog.geometry("1000x700")
        extract_dialog.transient(self.root)
        extract_dialog.grab_set()
        self.set_dialog_icon(extract_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(extract_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text="📝 PDF文本提取", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 创建文本显示区域
        text_frame = tk.Frame(dialog_frame, bg="white", highlightthickness=1, 
                             highlightbackground="#E0E0E0", highlightcolor="#64B5F6")
        text_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 15))
        
        # 文本显示区域
        extracted_text = scrolledtext.ScrolledText(
            text_frame, wrap=tk.WORD, 
            padx=15, pady=10, highlightthickness=0, border=0,
            font=self.viewer_font
        )
        extracted_text.pack(fill=tk.BOTH, expand=True)
        
        # 提取PDF文本
        try:
            all_text = ""
            for page_num in range(len(self.current_pdf)):
                page = self.current_pdf.load_page(page_num)
                text = page.get_text("text")
                all_text += f"--- 第 {page_num+1} 页 ---\n{text}\n\n"
            
            extracted_text.insert(tk.END, all_text)
        except Exception as e:
            messagebox.showerror("错误", f"提取PDF文本失败:\n{str(e)}")
            extracted_text.insert(tk.END, "文本提取失败")
        
        # 创建按钮区域
        button_frame = tk.Frame(dialog_frame, bg="white")
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        # 复制按钮
        copy_btn = tk.Button(button_frame, text="📋 复制文本", 
                            command=lambda: self.copy_to_clipboard(extracted_text), 
                            bg="#4CAF50", fg="white", bd=0, padx=20, pady=8)
        copy_btn.pack(side=tk.LEFT, padx=5)
        
        # 关闭按钮
        close_btn = tk.Button(button_frame, text="❌ 关闭", command=extract_dialog.destroy, 
                              bg="#F44336", fg="white", bd=0, padx=20, pady=8)
        close_btn.pack(side=tk.RIGHT, padx=5)
    
    def copy_to_clipboard(self, text_widget):
        """复制文本到剪贴板"""
        content = text_widget.get(1.0, tk.END)
        self.root.clipboard_clear()
        self.root.clipboard_append(content)
        messagebox.showinfo("成功", "文本已复制到剪贴板")
    
    def format_code(self):
        """格式化代码"""
        if self.current_pdf:
            messagebox.showinfo("提示", "PDF文件不支持格式化操作")
            return
            
        if not hasattr(self, 'text_viewer') or not self.text_viewer.winfo_ismapped():
            messagebox.showinfo("提示", "请先选择一个分类或文件")
            return
        
        # 临时启用文本编辑器以获取内容
        self.text_viewer.config(state="normal")
        content = self.text_viewer.get(1.0, tk.END)
        
        # 简单的格式化规则
        # 1. 移除行尾空格
        formatted_lines = [line.rstrip() for line in content.splitlines()]
        # 2. 确保文件以空行结束
        if formatted_lines and formatted_lines[-1] != '':
            formatted_lines.append('')
        
        formatted_content = '\n'.join(formatted_lines)
        
        # 更新内容
        self.text_viewer.delete(1.0, tk.END)
        self.text_viewer.insert(tk.END, formatted_content)
        
        # 应用语法高亮
        self.apply_syntax_highlighting()
        
        self.text_viewer.config(state="disabled")
        self.content_modified_flag = True
        self.status_var.set("代码已格式化")
    
    def add_snippet(self):
        """添加当前代码片段到收藏"""
        if not hasattr(self, 'text_viewer') or not self.text_viewer.winfo_ismapped():
            messagebox.showinfo("提示", "请先选择一个分类或文件")
            return
        
        # 获取当前选中的文本
        try:
            selected_text = self.text_viewer.get(tk.SEL_FIRST, tk.SEL_LAST)
        except:
            messagebox.showinfo("提示", "请先选择要收藏的代码片段")
            return
        
        # 弹出对话框让用户命名代码片段
        snippet_name = simpledialog.askstring("添加代码片段", "请输入代码片段名称:")
        if not snippet_name:
            return
        
        # 添加到收藏
        self.snippets[snippet_name] = selected_text
        self.save_snippets()
        messagebox.showinfo("成功", f"代码片段 '{snippet_name}' 已添加到收藏")
    
    def manage_snippets(self):
        """管理代码片段收藏"""
        if not self.snippets:
            messagebox.showinfo("提示", "当前没有收藏的代码片段")
            return
        
        # 创建管理对话框
        manage_dialog = tk.Toplevel(self.root)
        manage_dialog.title("管理代码片段")
        manage_dialog.geometry("800x600")
        manage_dialog.transient(self.root)
        manage_dialog.grab_set()
        self.set_dialog_icon(manage_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(manage_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text="🗂 管理代码片段", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 片段列表
        list_frame = tk.Frame(dialog_frame, bg="white")
        list_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 15))
        
        # 滚动条
        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 片段列表框
        snippet_list = tk.Listbox(
            list_frame, 
            bg="white", fg="#333", 
            selectbackground="#3498db", 
            highlightthickness=0, 
            borderwidth=1,
            relief="solid",
            font=("Segoe UI", 11),
            yscrollcommand=scrollbar.set
        )
        snippet_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=snippet_list.yview)
        
        # 添加片段到列表框
        for name in self.snippets.keys():
            snippet_list.insert(tk.END, name)
        
        # 创建按钮区域
        button_frame = tk.Frame(dialog_frame, bg="white")
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        # 查看按钮
        view_btn = tk.Button(button_frame, text="👁 查看片段", 
                            command=lambda: self.view_snippet(snippet_list.get(tk.ACTIVE)), 
                            bg="#3498db", fg="white", bd=0, padx=20, pady=8)
        view_btn.pack(side=tk.LEFT, padx=5)
        
        # 删除按钮
        delete_btn = tk.Button(button_frame, text="🗑 删除片段", 
                              command=lambda: self.delete_snippet(snippet_list, snippet_list.curselection()), 
                              bg="#F44336", fg="white", bd=0, padx=20, pady=8)
        delete_btn.pack(side=tk.LEFT, padx=5)
        
        # 关闭按钮
        close_btn = tk.Button(button_frame, text="❌ 关闭", command=manage_dialog.destroy, 
                              bg="#9E9E9E", fg="white", bd=0, padx=20, pady=8)
        close_btn.pack(side=tk.RIGHT, padx=5)
    
    def view_snippet(self, snippet_name):
        """查看代码片段"""
        if not snippet_name:
            messagebox.showinfo("提示", "请选择一个代码片段")
            return
        
        snippet_content = self.snippets.get(snippet_name, "")
        
        # 创建查看对话框
        view_dialog = tk.Toplevel(self.root)
        view_dialog.title(f"查看代码片段 - {snippet_name}")
        view_dialog.geometry("800x600")
        view_dialog.transient(self.root)
        view_dialog.grab_set()
        self.set_dialog_icon(view_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(view_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text=f"📋 代码片段: {snippet_name}", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 片段内容区域
        content_frame = tk.Frame(dialog_frame, bg="white", highlightthickness=1, 
                                highlightbackground="#E0E0E0", highlightcolor="#64B5F6")
        content_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 15))
        
        # 片段内容显示
        snippet_text = scrolledtext.ScrolledText(
            content_frame, wrap=tk.WORD, 
            padx=15, pady=10, highlightthickness=0, border=0,
            font=self.viewer_font
        )
        snippet_text.pack(fill=tk.BOTH, expand=True)
        snippet_text.insert(tk.END, snippet_content)
        snippet_text.config(state="disabled")
        
        # 创建按钮区域
        button_frame = tk.Frame(dialog_frame, bg="white")
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        # 复制按钮
        copy_btn = tk.Button(button_frame, text="📋 复制片段", 
                            command=lambda: self.copy_snippet(snippet_content), 
                            bg="#4CAF50", fg="white", bd=0, padx=20, pady=8)
        copy_btn.pack(side=tk.LEFT, padx=5)
        
        # 关闭按钮
        close_btn = tk.Button(button_frame, text="❌ 关闭", command=view_dialog.destroy, 
                              bg="#9E9E9E", fg="white", bd=0, padx=20, pady=8)
        close_btn.pack(side=tk.RIGHT, padx=5)
    
    def copy_snippet(self, content):
        """复制代码片段到剪贴板"""
        self.root.clipboard_clear()
        self.root.clipboard_append(content)
        messagebox.showinfo("成功", "代码片段已复制到剪贴板")
    
    def delete_snippet(self, snippet_list, selection):
        """删除选中的代码片段"""
        if not selection:
            messagebox.showinfo("提示", "请选择一个代码片段")
            return
        
        snippet_name = snippet_list.get(selection)
        if messagebox.askyesno("确认删除", f"确定要删除代码片段 '{snippet_name}' 吗？"):
            del self.snippets[snippet_name]
            snippet_list.delete(selection)
            self.save_snippets()
            messagebox.showinfo("成功", f"代码片段 '{snippet_name}' 已删除")
    
    def save_snippets(self):
        """保存代码片段到文件"""
        config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "snippets.json")
        try:
            with open(config_path, "w", encoding="utf-8") as f:
                json.dump(self.snippets, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"保存代码片段失败: {str(e)}")
    
    def load_snippets(self):
        """从文件加载代码片段"""
        config_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "snippets.json")
        # 如果配置文件不存在，则创建空字典
        if not os.path.exists(config_path):
            self.snippets = {}
            return
        try:
            with open(config_path, "r", encoding="utf-8") as f:
                self.snippets = json.load(f)
        except Exception as e:
            print(f"加载代码片段失败: {str(e)}")
            self.snippets = {}

    def toggle_auto_save(self):
        """切换自动保存开关"""
        self.auto_save_enabled = self.auto_save_var.get()
        if self.auto_save_enabled:
            self.start_auto_save()
            self.status_var.set("自动保存已启用")
        else:
            self.stop_auto_save()
            self.status_var.set("自动保存已关闭")
    
    def start_auto_save(self):
        """启动自动保存线程"""
        if self.auto_save_thread is None or not self.auto_save_thread.is_alive():
            self.auto_save_event.clear()  # 新增
            self.auto_save_thread = threading.Thread(target=self.auto_save, daemon=True)
            self.auto_save_running = True
            self.auto_save_thread.start()
            self.status_var.set("自动保存已启用")
    
    def stop_auto_save(self):
        """停止自动保存"""
        self.auto_save_running = False
        self.auto_save_event.set()  # 新增，唤醒线程
        if self.auto_save_thread and self.auto_save_thread.is_alive():
            self.auto_save_thread.join(timeout=2.0)
    
    def auto_save(self):
        """自动保存当前内容"""
        while self.auto_save_running and self.auto_save_enabled:
            # 等待指定的时间间隔，期间可被唤醒
            self.auto_save_event.wait(self.auto_save_interval / 1000)
            if not self.auto_save_running or not self.auto_save_enabled:
                break
                
            # 检查是否需要保存
            if (self.content_modified_flag and self.current_file_path and 
                not self.current_pdf and hasattr(self, 'text_viewer')):
                try:
                    # 保存文件
                    self.text_viewer.config(state="normal")
                    content = self.text_viewer.get(1.0, tk.END)
                    self.text_viewer.config(state="disabled")
                    
                    with open(self.current_file_path, "w", encoding="utf-8") as file:
                        file.write(content)
                    
                    self.content_modified_flag = False
                    self.status_var.set(f"自动保存成功: {os.path.basename(self.current_file_path)}")
                except Exception as e:
                    self.status_var.set(f"自动保存失败: {str(e)}")
    
    def update_word_count(self):
        """更新字数统计"""
        if not hasattr(self, 'text_viewer') or not self.text_viewer.winfo_ismapped():
            return
        
        # 临时启用文本编辑器以获取内容
        self.text_viewer.config(state="normal")
        content = self.text_viewer.get(1.0, "end-1c")  # 排除最后的换行符
        self.text_viewer.config(state="disabled")
        
        # 计算字数（中文字符+英文单词）
        chinese_chars = len(re.findall(r'[\u4e00-\u9fff]', content))
        english_words = len(re.findall(r'\b\w+\b', content))
        total_words = chinese_chars + english_words
        
        # 更新显示
        self.word_count_var.set(f"字数: {total_words}")

    # =============== 笔记功能新增方法 ===============
    def take_note(self):
        """创建新笔记"""
        note_dialog = tk.Toplevel(self.root)
        note_dialog.title("新建笔记")
        note_dialog.geometry("1792x1008")
        note_dialog.transient(self.root)
        note_dialog.grab_set()
        self.set_dialog_icon(note_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(note_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text="📝 新建笔记", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 笔记标题
        title_frame = tk.Frame(dialog_frame, bg="white")
        title_frame.pack(fill=tk.X, pady=(0, 10))
        
        tk.Label(title_frame, text="标题:", bg="white", font=("Segoe UI", 12)).pack(side=tk.LEFT)
        note_title = tk.Entry(title_frame, font=("Segoe UI", 12), width=50)
        note_title.pack(side=tk.LEFT, padx=10, fill=tk.X, expand=True)
        note_title.focus()
        
        # 笔记内容
        content_frame = tk.Frame(dialog_frame, bg="white", highlightthickness=1, 
                               highlightbackground="#E0E0E0", highlightcolor="#64B5F6")
        content_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        note_content = scrolledtext.ScrolledText(
            content_frame, wrap=tk.WORD, 
            padx=15, pady=10, highlightthickness=0, border=0,
            font=("Segoe UI", 12)
        )
        note_content.pack(fill=tk.BOTH, expand=True)
        
        # 创建按钮区域
        button_frame = tk.Frame(dialog_frame, bg="white")
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        # 保存按钮
        save_btn = tk.Button(button_frame, text="💾 保存笔记", 
                            command=lambda: self.save_note(note_dialog, note_title.get(), note_content.get("1.0", tk.END)), 
                            bg="#4CAF50", fg="white", bd=0, padx=20, pady=8)
        save_btn.pack(side=tk.LEFT, padx=5)
        
        # 取消按钮
        cancel_btn = tk.Button(button_frame, text="❌ 取消", command=note_dialog.destroy, 
                              bg="#F44336", fg="white", bd=0, padx=20, pady=8)
        cancel_btn.pack(side=tk.RIGHT, padx=5)
    
    def save_note(self, dialog, title, content):
        """保存笔记"""
        if not title.strip():
            messagebox.showwarning("警告", "笔记标题不能为空")
            return
            
        # 创建笔记ID
        note_id = self.next_note_id
        self.next_note_id += 1
        
        # 获取当前时间
        now = datetime.datetime.now()
        created_at = now.strftime("%Y-%m-%d %H:%M:%S")
        updated_at = created_at
        
        # 保存笔记
        self.notes[note_id] = {
            "title": title,
            "content": content,
            "created_at": created_at,
            "updated_at": updated_at
        }
        
        # 保存到文件
        self.save_notes()
        
        # 关闭对话框
        dialog.destroy()
        
        # 显示成功消息
        messagebox.showinfo("成功", f"笔记 '{title}' 已保存")
        self.status_var.set(f"笔记已保存: {title}")
        
        # 打开笔记查看
        self.open_note(note_id)
    
    def open_note(self, note_id):
        """打开笔记查看"""
        if note_id not in self.notes:
            messagebox.showerror("错误", "笔记不存在")
            return
            
        note = self.notes[note_id]
        self.current_note_id = note_id
        
        # 显示文本查看器
        self.show_text_viewer()
        
        # 更新标题
        self.title_label.configure(text=f"笔记查看器 - {note['title']}")
        
        # 加载笔记内容
        self.text_viewer.config(state="normal")
        self.text_viewer.delete(1.0, tk.END)
        self.text_viewer.insert(tk.END, note['content'])
        self.text_viewer.config(state="disabled")  # 设置为只读
        
        # 更新状态
        self.status_var.set(f"已打开笔记: {note['title']} | 创建时间: {note['created_at']}")
        
        # 更新行号和字数
        self.update_fixed_line_numbers()
        self.update_word_count()
        
        # 清空输出面板
        self.clear_output()
    
    def manage_notes(self):
        """管理笔记"""
        if not self.notes:
            messagebox.showinfo("提示", "当前没有笔记")
            return
        
        # 创建管理对话框
        manage_dialog = tk.Toplevel(self.root)
        manage_dialog.title("管理笔记")
        manage_dialog.geometry("800x600")
        manage_dialog.transient(self.root)
        manage_dialog.grab_set()
        self.set_dialog_icon(manage_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(manage_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text="🗂 管理笔记", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 笔记列表
        list_frame = tk.Frame(dialog_frame, bg="white")
        list_frame.pack(fill=tk.BOTH, expand=True, pady=(0, 15))
        
        # 滚动条
        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 笔记列表框
        notes_list = tk.Listbox(
            list_frame, 
            bg="white", fg="#333", 
            selectbackground="#3498db", 
            highlightthickness=0, 
            borderwidth=1,
            relief="solid",
            font=("Segoe UI", 12),
            yscrollcommand=scrollbar.set
        )
        notes_list.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.config(command=notes_list.yview)
        
        # 添加笔记到列表框
        for note_id, note in self.notes.items():
            notes_list.insert(tk.END, f"{note['title']} (创建于: {note['created_at']})")
            notes_list.note_ids = getattr(notes_list, 'note_ids', [])  # 动态属性存储笔记ID
            notes_list.note_ids.append(note_id)
        
        # 创建按钮区域
        button_frame = tk.Frame(dialog_frame, bg="white")
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        # 查看按钮
        view_btn = tk.Button(button_frame, text="👁 查看笔记", 
                            command=lambda: self.open_selected_note(notes_list), 
                            bg="#3498db", fg="white", bd=0, padx=20, pady=8)
        view_btn.pack(side=tk.LEFT, padx=5)
        
        # 编辑按钮
        edit_btn = tk.Button(button_frame, text="✏ 编辑笔记", 
                            command=lambda: self.edit_selected_note(notes_list), 
                            bg="#f39c12", fg="white", bd=0, padx=20, pady=8)
        edit_btn.pack(side=tk.LEFT, padx=5)
        
        # 删除按钮
        delete_btn = tk.Button(button_frame, text="🗑 删除笔记", 
                              command=lambda: self.delete_selected_note(notes_list), 
                              bg="#F44336", fg="white", bd=0, padx=20, pady=8)
        delete_btn.pack(side=tk.LEFT, padx=5)
        
        # 关闭按钮
        close_btn = tk.Button(button_frame, text="❌ 关闭", command=manage_dialog.destroy, 
                              bg="#9E9E9E", fg="white", bd=0, padx=20, pady=8)
        close_btn.pack(side=tk.RIGHT, padx=5)
    
    def open_selected_note(self, notes_list):
        """打开选中的笔记"""
        selection = notes_list.curselection()
        if not selection:
            messagebox.showinfo("提示", "请选择一个笔记")
            return
        
        note_id = notes_list.note_ids[selection[0]]
        self.open_note(note_id)
    
    def edit_selected_note(self, notes_list):
        """编辑选中的笔记"""
        selection = notes_list.curselection()
        if not selection:
            messagebox.showinfo("提示", "请选择一个笔记")
            return
        
        note_id = notes_list.note_ids[selection[0]]
        note = self.notes[note_id]
        
        note_dialog = tk.Toplevel(self.root)
        note_dialog.title("编辑笔记")
        note_dialog.geometry("1000x700")
        note_dialog.transient(self.root)
        note_dialog.grab_set()
        self.set_dialog_icon(note_dialog)
        
        # 创建对话框框架
        dialog_frame = tk.Frame(note_dialog, bg="white", padx=20, pady=20)
        dialog_frame.pack(fill=tk.BOTH, expand=True)
        
        # 标题
        title_label = tk.Label(dialog_frame, text="✏ 编辑笔记", 
                             bg="white", fg="#333", 
                             font=("Segoe UI", 16, "bold"))
        title_label.pack(pady=(0, 15))
        
        # 笔记标题
        title_frame = tk.Frame(dialog_frame, bg="white")
        title_frame.pack(fill=tk.X, pady=(0, 10))
        
        tk.Label(title_frame, text="标题:", bg="white", font=("Segoe UI", 12)).pack(side=tk.LEFT)
        note_title = tk.Entry(title_frame, font=("Segoe UI", 12), width=50)
        note_title.pack(side=tk.LEFT, padx=10, fill=tk.X, expand=True)
        note_title.insert(0, note['title'])
        note_title.focus()
        
        # 笔记内容
        content_frame = tk.Frame(dialog_frame, bg="white", highlightthickness=1, 
                               highlightbackground="#E0E0E0", highlightcolor="#64B5F6")
        content_frame.pack(fill=tk.BOTH, expand=True, pady=10)
        
        note_content = scrolledtext.ScrolledText(
            content_frame, wrap=tk.WORD, 
            padx=15, pady=10, highlightthickness=0, border=0,
            font=("Segoe UI", 12)
        )
        note_content.pack(fill=tk.BOTH, expand=True)
        note_content.insert(tk.END, note['content'])
        
        # 创建按钮区域
        button_frame = tk.Frame(dialog_frame, bg="white")
        button_frame.pack(fill=tk.X, pady=(10, 0))
        
        # 保存按钮
        save_btn = tk.Button(button_frame, text="💾 保存修改", 
                            command=lambda: self.update_note(note_dialog, note_id, note_title.get(), note_content.get("1.0", tk.END)), 
                            bg="#4CAF50", fg="white", bd=0, padx=20, pady=8)
        save_btn.pack(side=tk.LEFT, padx=5)
        
        # 取消按钮
        cancel_btn = tk.Button(button_frame, text="❌ 取消", command=note_dialog.destroy, 
                              bg="#F44336", fg="white", bd=0, padx=20, pady=8)
        cancel_btn.pack(side=tk.RIGHT, padx=5)
    
    def update_note(self, dialog, note_id, title, content):
        """更新笔记内容"""
        if not title.strip():
            messagebox.showwarning("警告", "笔记标题不能为空")
            return
            
        if note_id not in self.notes:
            messagebox.showerror("错误", "笔记不存在")
            return
            
        # 更新笔记
        self.notes[note_id]['title'] = title
        self.notes[note_id]['content'] = content
        self.notes[note_id]['updated_at'] = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        
        # 保存到文件
        self.save_notes()
        
        # 关闭对话框
        dialog.destroy()
        
        # 显示成功消息
        messagebox.showinfo("成功", f"笔记 '{title}' 已更新")
        self.status_var.set(f"笔记已更新: {title}")
        
        # 如果当前打开的是这个笔记，更新显示
        if self.current_note_id == note_id:
            self.open_note(note_id)
    
    def delete_selected_note(self, notes_list):
        """删除选中的笔记"""
        selection = notes_list.curselection()
        if not selection:
            messagebox.showinfo("提示", "请选择一个笔记")
            return
            
        note_id = notes_list.note_ids[selection[0]]
        note_title = self.notes[note_id]['title']
        
        if messagebox.askyesno("确认删除", f"确定要删除笔记 '{note_title}' 吗？"):
            del self.notes[note_id]
            self.save_notes()
            
            # 从列表框中删除
            notes_list.delete(selection[0])
            del notes_list.note_ids[selection[0]]
            
            # 如果当前打开的是这个笔记，关闭它
            if self.current_note_id == note_id:
                self.current_note_id = None
                self.show_home()
            
            messagebox.showinfo("成功", f"笔记 '{note_title}' 已删除")
    
    def save_notes(self):
        """保存笔记到文件"""
        notes_path = os.path.join(self.notes_dir, "notes.json")
        try:
            with open(notes_path, "w", encoding="utf-8") as f:
                # 保存笔记数据和下一个ID
                data = {
                    "notes": self.notes,
                    "next_note_id": self.next_note_id
                }
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print(f"保存笔记失败: {str(e)}")
    
    def load_notes(self):
        """从文件加载笔记"""
        notes_path = os.path.join(self.notes_dir, "notes.json")
        
        # 如果笔记文件不存在，则初始化
        if not os.path.exists(notes_path):
            self.notes = {}
            self.next_note_id = 1
            return
        
        try:
            with open(notes_path, "r", encoding="utf-8") as f:
                data = json.load(f)
                self.notes = data.get("notes", {})
                self.next_note_id = data.get("next_note_id", 1)
        except Exception as e:
            print(f"加载笔记失败: {str(e)}")
            self.notes = {}
            self.next_note_id = 1

    # =============== 运行代码功能新增方法 ===============
    def run_python_code(self):
        """运行当前Python代码"""
        # 如果是PDF文件，不能运行
        if self.current_pdf:
            messagebox.showinfo("提示", "PDF文件不支持代码运行")
            return
            
        if not hasattr(self, 'text_viewer') or not self.text_viewer.winfo_ismapped():
            messagebox.showinfo("提示", "请先选择一个分类或文件")
            return
        
        # 检查是否Python文件
        if not self.is_python_content():
            messagebox.showinfo("提示", "当前内容不是Python代码，无法运行")
            return
        
        # 清空输出面板
        self.clear_output()
        
        # 获取代码内容
        self.text_viewer.config(state="normal")
        code = self.text_viewer.get("1.0", tk.END)
        self.text_viewer.config(state="disabled")
        
        # 更新状态
        self.run_status_var.set("运行中...")
        self.status_var.set("正在运行Python代码...")
        
        # 在新线程中运行代码
        threading.Thread(target=self.execute_code, args=(code,), daemon=True).start()
    
    def is_python_content(self):
        """检查当前内容是否是Python代码"""
        # 根据文件扩展名或内容判断
        if self.current_file_path and self.current_file_path.lower().endswith('.py'):
            return True
        
        # 如果没有文件路径，检查内容中是否有Python关键字
        content = self.text_viewer.get("1.0", "1.100")
        if any(keyword in content for keyword in ["import", "def", "class", "print"]):
            return True
        
        return False
    
    def execute_code(self, code):
        """在新线程中执行代码"""
        try:
            # 创建字符串IO对象用于捕获输出
            output_buffer = io.StringIO()
            
            # 重定向标准输出
            with contextlib.redirect_stdout(output_buffer):
                # 执行代码
                exec(code, {})
            
            # 获取输出
            output = output_buffer.getvalue()
            
            # 在UI线程中更新输出
            self.root.after(0, lambda: self.display_output(output, "执行成功"))
        except Exception as e:
            # 在UI线程中显示错误
            self.root.after(0, lambda: self.display_output(str(e), "执行出错", is_error=True))
    
    def display_output(self, output, status, is_error=False):
        """在输出面板显示执行结果"""
        # 确保输出面板可见
        if not self.output_panel_visible:
            self.toggle_output_panel()
        
        # 启用输出面板
        self.output_text.config(state="normal")
        
        # 插入分隔线和时间戳
        now = datetime.datetime.now().strftime("%H:%M:%S")
        self.output_text.insert(tk.END, f"\n\n--- 输出 [{now}] ---\n")
        
        # 插入输出内容
        if is_error:
            self.output_text.insert(tk.END, f"错误:\n{output}")
            self.output_text.tag_add("error", "1.0", tk.END)
            self.output_text.tag_configure("error", foreground="#e74c3c")
        else:
            self.output_text.insert(tk.END, output)
        
        # 禁用编辑
        self.output_text.config(state="disabled")
        
        # 滚动到最后
        self.output_text.see(tk.END)
        
        # 更新状态
        self.run_status_var.set(status)
        self.status_var.set(f"操作完成: {status}")
    
    def clear_output(self):
        """清空输出面板"""
        self.output_text.config(state="normal")
        self.output_text.delete("1.0", tk.END)
        self.output_text.config(state="disabled")
        self.run_status_var.set("就绪")

def main():
    root = tk.Tk()
    
    # 主页面背景
    root.configure(bg="#f0f2f5")

    try:
        # 使用base64编码的应用图标
        icon_data = """
        R0lGODlhEAAQAMQAAOjo6KWlpaampqenp6qqqqurq6ysrK2tra6urq+vr7CwsLGxsbKysrOzs7S0
        tLW1tba2tre3t7i4uLm5ubq6uru7u7y8vL29vb6+vr+/v8DAwMHBwcLCwsPDw8TExMXFxcbGxsfH
        x8jIyMnJycrKysvLy8zMzM3Nzc7Ozs/Pz9DQ0NHR0dLS0tPT09TU1NXV1dbW1tfX19jY2NnZ2dra
        2tvb29zc3N3d3d7e3t/f3+Dg4OHh4eLi4uPj4+Tk5OXl5ebm5ufn5+jo6Onp6erq6uvr6+zs7O3t
        7e7u7u/v7/Dw8PHx8fLy8vPz8/T09PX19fb29vf39/j4+Pn5+fr6+vv7+/z8/P39/f7+/v///yH5
        BAAAAAAALAAAAAAQABAAAAVqICCOZGmeaKqubOu+cCzPdG3feK7vfO//wKBwSCwaj8ikcslsOp/Q
        qHRKrVqv2Kx2y+16v+CweEwum8/otHrNbrvf8Lh8Tq/b7/i8fs/v+/+AgYKDhIWGh4iJiouMjY6P
        kJGSk5SVlhcAOw==
        """
        icon_bytes = base64.b64decode(icon_data)
        icon_photo = tk.PhotoImage(data=icon_bytes)
        root.iconphoto(True, icon_photo)
    except:
        pass
    
    app = EnhancedTextViewer(root)
    root.mainloop()

if __name__ == "__main__":
    main()
