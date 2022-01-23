import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.io.IOException;
import java.io.File;
import java.nio.file.Path;
import java.nio.file.Paths;

import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import com.jfinal.core.Controller;

public class FilePathInjection extends Controller {
	private static final String BASE_PATH = "/pages";

	// BAD: Upload file to user specified path without validation
	public void uploadFile() throws IOException {
		String savePath = getPara("dir");
		File file = getFile("fileParam").getFile();
		String finalFilePath = BASE_PATH + savePath;

		FileInputStream fis = new FileInputStream(file);
		FileOutputStream fos = new FileOutputStream(finalFilePath);
		int i = 0;

		do {
			byte[] buf = new byte[1024];
			i = fis.read(buf);
			fos.write(buf);
		} while (i != -1);
		
		fis.close();
		fos.close();
	}

	// GOOD: Upload file to user specified path with path normalization and validation
	public void uploadFile2() throws IOException {
		String savePath = getPara("dir");
		File file = getFile("fileParam").getFile();
		String finalFilePath = BASE_PATH + savePath;
		Path path = Paths.get(finalFilePath).normalize();

		if (path.startsWith(BASE_PATH)) {
			FileInputStream fis = new FileInputStream(file);
			FileOutputStream fos = new FileOutputStream(path.toFile());
			int i = 0;

			do {
				byte[] buf = new byte[1024];
				i = fis.read(buf);
				fos.write(buf);
			} while (i != -1);
			
			fis.close();
			fos.close();
		}
	}

	private void readFile(HttpServletResponse resp, File file) {
		OutputStream os = null;
		FileInputStream fis = null;
		try {
			os = resp.getOutputStream();
			fis = new FileInputStream(file);
			byte fileContent[] = new byte[(int) file.length()];
			fis.read(fileContent);
			os.write(fileContent);
		} catch (Exception e) {
			System.err.println("Invalid directory or file " + file.getName());
		} finally {
			try {
				if (os != null)
					os.close();
			} catch (Exception e2) {
			}
			try {
				if (fis != null)
					fis.close();
			} catch (Exception e2) {
			}
		}
	}

	public void downloadFile() throws FileNotFoundException, IOException {
		HttpServletRequest request = getRequest();
		String path = request.getParameter("path");
		String filePath = BASE_PATH + path;

		HttpServletResponse resp = getResponse();
		File file = new File(filePath);
		if (path != null && file.exists()) {
			resp.setHeader("Content-type", "application/force-download");
			resp.setHeader("Content-Disposition", "inline;filename=\"" + filePath + "\"");
			resp.setHeader("Content-Transfer-Encoding", "Binary");
			resp.setHeader("Content-length", "" + file.length());
			resp.setHeader("Content-Type", "application/octet-stream");
			resp.setHeader("Content-Disposition", "attachment; filename=\"" + file.getName() + "\"");
			readFile(resp, file);
		} else {
			System.err.println("File does not exist " + path);
		}
	}

	public void downloadFile2() throws FileNotFoundException, IOException {
		HttpServletRequest request = getRequest();
		String path = request.getParameter("path");
		String filePath = BASE_PATH + path;

		HttpServletResponse resp = getResponse();
		if (!filePath.contains("..") && filePath.startsWith(BASE_PATH)) {
			File file = new File(filePath);
			if (file.exists()) {
				resp.setHeader("Content-type", "application/force-download");
				resp.setHeader("Content-Disposition", "inline;filename=\"" + filePath + "\"");
				resp.setHeader("Content-Transfer-Encoding", "Binary");
				resp.setHeader("Content-length", "" + file.length());
				resp.setHeader("Content-Type", "application/octet-stream");
				resp.setHeader("Content-Disposition", "attachment; filename=\"" + file.getName() + "\"");
				readFile(resp, file);
			} else {
				System.err.println("File does not exist " + path);
			}
		}
	}
}
